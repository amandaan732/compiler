import sparrow.*;
import IR.SparrowParser;
import IR.visitor.SparrowConstructor;

import sparrow.*;
import IR.token.Identifier;
import java.util.*;

/**
 * S2SV: Sparrow -> Sparrow-V
 *
 * Clean rewrite with all optimizations integrated from the start:
 *
 * F1  - Backward dataflow liveness
 * A2  - Chordal coloring (MCS + reverse PEO greedy)
 * C1  - Caller-saved (t2-t5) for non-spanning vars
 * C2  - Callee-saved (s1-s11) for call-spanning vars
 * C3  - Save only USED s-regs
 * C4  - Save only LIVE t-regs at each call site
 * S1  - t0/t1 reserved as scratch
 * S2  - Spill-victim: lowest spill cost
 * S3  - Loop-depth-weighted spill cost (10^depth)
 * M1  - Conservative move coalescing
 * P1  - Rematerialize constants/func-refs
 * P2  - Dead-code elimination
 *
 * Key architectural decisions:
 * - Plain identifier saves for s-regs (NO heap frame/alloc)
 * - liveIn ∩ liveOut for spanning (C2 definition)
 * - Spilled args passed directly to calls (no _a slot needed)
 * - diesAtCallArg vars prefer to stay spilled
 */
public class S2SV {

    static final String T0 = "t0", T1 = "t1"; // scratch, never allocated
    static final List<String> CALLER_T = Arrays.asList("t2","t3","t4","t5");
    static final List<String> CALLEE_S = Arrays.asList(
        "s1","s2","s3","s4","s5","s6","s7","s8","s9","s10","s11");

    static int uid = 0;

    public static void main(String[] args) throws Exception {
        new SparrowParser(System.in);
        IR.syntaxtree.Program tree = SparrowParser.Program();
        SparrowConstructor ctor = new SparrowConstructor();
        tree.accept(ctor);
        sparrow.Program prog = ctor.getProgram();
        StringBuilder out = new StringBuilder();
        for (FunctionDecl fn : prog.funDecls)
            compileFunction(fn, out);
        System.out.print(out);
    }

    // =========================================================================
    // F1: Backward dataflow liveness
    // =========================================================================
    static class Liveness {
        List<Set<String>> in, out, def, use;
        Map<String,Integer> labelIdx = new HashMap<>();
    }

    static Liveness liveness(List<Instruction> instrs,
                              List<Identifier> params,
                              Identifier retId) {
        int n = instrs.size();
        Liveness lv = new Liveness();
        lv.in  = new ArrayList<>(); lv.out = new ArrayList<>();
        lv.def = new ArrayList<>(); lv.use = new ArrayList<>();

        for (int i = 0; i < n; i++) {
            if (instrs.get(i) instanceof LabelInstr)
                lv.labelIdx.put(((LabelInstr)instrs.get(i)).label.toString(), i);
            Set<String> d = new LinkedHashSet<>(), u = new LinkedHashSet<>();
            defUse(instrs.get(i), d, u);
            lv.def.add(d); lv.use.add(u);
            lv.in.add(new LinkedHashSet<>()); lv.out.add(new LinkedHashSet<>());
        }

        Set<String> retSet = new LinkedHashSet<>();
        if (retId != null) retSet.add(retId.toString());

        boolean changed = true;
        while (changed) {
            changed = false;
            for (int i = n-1; i >= 0; i--) {
                Set<String> newOut = new LinkedHashSet<>();
                Instruction ins = instrs.get(i);
                if (ins instanceof sparrow.Goto) {
                    Integer t = lv.labelIdx.get(((sparrow.Goto)ins).label.toString());
                    if (t != null) newOut.addAll(lv.in.get(t));
                } else if (ins instanceof IfGoto) {
                    Integer t = lv.labelIdx.get(((IfGoto)ins).label.toString());
                    if (t != null) newOut.addAll(lv.in.get(t));
                    if (i+1 < n) newOut.addAll(lv.in.get(i+1));
                } else if (ins instanceof ErrorMessage) {
                    // no successors
                } else {
                    if (i+1 < n) newOut.addAll(lv.in.get(i+1));
                    else newOut.addAll(retSet);
                }
                if (i == n-1) newOut.addAll(retSet);

                Set<String> newIn = new LinkedHashSet<>(lv.use.get(i));
                for (String v : newOut) if (!lv.def.get(i).contains(v)) newIn.add(v);

                if (!newOut.equals(lv.out.get(i)) || !newIn.equals(lv.in.get(i))) {
                    lv.out.set(i, newOut); lv.in.set(i, newIn); changed = true;
                }
            }
        }
        return lv;
    }

    static void defUse(Instruction ins, Set<String> def, Set<String> use) {
        if      (ins instanceof Move_Id_Integer)  def.add(((Move_Id_Integer)ins).lhs.toString());
        else if (ins instanceof Move_Id_FuncName) def.add(((Move_Id_FuncName)ins).lhs.toString());
        else if (ins instanceof Move_Id_Id) {
            Move_Id_Id m = (Move_Id_Id)ins;
            def.add(m.lhs.toString()); use.add(m.rhs.toString());
        } else if (ins instanceof Add) {
            Add a = (Add)ins;
            def.add(a.lhs.toString()); use.add(a.arg1.toString()); use.add(a.arg2.toString());
        } else if (ins instanceof Subtract) {
            Subtract s = (Subtract)ins;
            def.add(s.lhs.toString()); use.add(s.arg1.toString()); use.add(s.arg2.toString());
        } else if (ins instanceof Multiply) {
            Multiply m = (Multiply)ins;
            def.add(m.lhs.toString()); use.add(m.arg1.toString()); use.add(m.arg2.toString());
        } else if (ins instanceof LessThan) {
            LessThan lt = (LessThan)ins;
            def.add(lt.lhs.toString()); use.add(lt.arg1.toString()); use.add(lt.arg2.toString());
        } else if (ins instanceof Load) {
            Load l = (Load)ins; def.add(l.lhs.toString()); use.add(l.base.toString());
        } else if (ins instanceof Store) {
            Store s = (Store)ins; use.add(s.base.toString()); use.add(s.rhs.toString());
        } else if (ins instanceof Alloc) {
            Alloc a = (Alloc)ins; def.add(a.lhs.toString()); use.add(a.size.toString());
        } else if (ins instanceof Print)  { use.add(((Print)ins).content.toString()); }
        else if (ins instanceof IfGoto)   { use.add(((IfGoto)ins).condition.toString()); }
        else if (ins instanceof Call) {
            Call c = (Call)ins; def.add(c.lhs.toString()); use.add(c.callee.toString());
            for (Identifier a : c.args) use.add(a.toString());
        }
    }

    // =========================================================================
    // P2: Dead-code elimination
    // =========================================================================
    static List<Instruction> dce(List<Instruction> instrs,
                                  List<Identifier> params,
                                  Identifier retId) {
        boolean changed = true;
        List<Instruction> cur = new ArrayList<>(instrs);
        while (changed) {
            changed = false;
            Liveness lv = liveness(cur, params, retId);
            List<Instruction> next = new ArrayList<>();
            for (int i = 0; i < cur.size(); i++) {
                Instruction ins = cur.get(i);
                boolean pure = (ins instanceof Move_Id_Integer ||
                                ins instanceof Move_Id_FuncName ||
                                ins instanceof Move_Id_Id ||
                                ins instanceof Add || ins instanceof Subtract ||
                                ins instanceof Multiply || ins instanceof LessThan);
                if (pure && !lv.def.get(i).isEmpty()) {
                    final Set<String> outI = lv.out.get(i);
                    boolean dead = lv.def.get(i).stream()
                        .noneMatch(d -> outI.contains(d));
                    if (dead) { changed = true; continue; }
                }
                next.add(ins);
            }
            cur = next;
        }
        return cur;
    }

    // =========================================================================
    // P1: Rematerializable vars (single def, constant or func-ref)
    // =========================================================================
    static Map<String,Instruction> findRemat(List<Instruction> instrs,
                                              List<Identifier> params) {
        Set<String> paramSet = new HashSet<>();
        for (Identifier p : params) paramSet.add(p.toString());
        Map<String,Integer> defCnt = new HashMap<>();
        Map<String,Instruction> defIns = new HashMap<>();
        for (Instruction ins : instrs) {
            boolean cheap = (ins instanceof Move_Id_Integer || ins instanceof Move_Id_FuncName);
            Set<String> d = new LinkedHashSet<>();
            defUse(ins, d, new LinkedHashSet<>());
            for (String v : d) {
                defCnt.merge(v, 1, Integer::sum);
                if (cheap && !paramSet.contains(v)) defIns.put(v, ins);
            }
        }
        Map<String,Instruction> remat = new HashMap<>();
        for (Map.Entry<String,Instruction> e : defIns.entrySet())
            if (defCnt.getOrDefault(e.getKey(), 0) == 1) remat.put(e.getKey(), e.getValue());
        return remat;
    }

    // =========================================================================
    // S3: Loop-depth-weighted spill cost
    // =========================================================================
    static Map<String,Double> spillCosts(List<Instruction> instrs) {
        int n = instrs.size();
        int[] depth = new int[n];
        Map<String,Integer> labelIdx = new HashMap<>();
        for (int i = 0; i < n; i++)
            if (instrs.get(i) instanceof LabelInstr)
                labelIdx.put(((LabelInstr)instrs.get(i)).label.toString(), i);
        for (int i = 0; i < n; i++) {
            String tgt = null;
            Instruction ins = instrs.get(i);
            if (ins instanceof sparrow.Goto) tgt = ((sparrow.Goto)ins).label.toString();
            else if (ins instanceof IfGoto)  tgt = ((IfGoto)ins).label.toString();
            if (tgt != null) {
                Integer t = labelIdx.get(tgt);
                if (t != null && t <= i)
                    for (int k = t; k <= i; k++) depth[k]++;
            }
        }
        Map<String,Double> cost = new HashMap<>();
        for (int i = 0; i < n; i++) {
            double w = Math.pow(10.0, depth[i]);
            Set<String> d = new LinkedHashSet<>(), u = new LinkedHashSet<>();
            defUse(instrs.get(i), d, u);
            Set<String> all = new LinkedHashSet<>(d); all.addAll(u);
            for (String v : all) cost.merge(v, w, Double::sum);
        }
        return cost;
    }

    // =========================================================================
    // Variable classification
    // =========================================================================

    /** C2: vars live across at least one call (liveIn ∩ liveOut), excluding remat */
    static Set<String> callSpanning(List<Instruction> instrs, Liveness lv,
                                     Map<String,Instruction> remat) {
        Set<String> span = new HashSet<>();
        for (int i = 0; i < instrs.size(); i++)
            if (instrs.get(i) instanceof Call) {
                Set<String> cross = new HashSet<>(lv.in.get(i));
                cross.retainAll(lv.out.get(i));
                cross.removeAll(remat.keySet());
                span.addAll(cross);
            }
        return span;
    }

    /** diesAtCallArg: last use is as call arg and dead after that call */
    static Set<String> findDiesAtCallArg(List<Instruction> instrs, Liveness lv) {
        Map<String,Integer> lastIdx  = new HashMap<>();
        Map<String,Boolean> lastIsArg = new HashMap<>();
        for (int i = 0; i < instrs.size(); i++) {
            Instruction ins = instrs.get(i);
            if (ins instanceof Call) {
                Call c = (Call)ins;
                lastIdx.put(c.callee.toString(), i);
                lastIsArg.put(c.callee.toString(), false);
                for (Identifier a : c.args) {
                    lastIdx.put(a.toString(), i);
                    lastIsArg.put(a.toString(), true);
                }
            } else {
                Set<String> u = new LinkedHashSet<>();
                defUse(ins, new LinkedHashSet<>(), u);
                for (String v : u) { lastIdx.put(v, i); lastIsArg.put(v, false); }
            }
        }
        Set<String> dies = new HashSet<>();
        for (Map.Entry<String,Integer> e : lastIdx.entrySet()) {
            String v = e.getKey(); int i = e.getValue();
            if (Boolean.TRUE.equals(lastIsArg.get(v)) && !lv.out.get(i).contains(v))
                dies.add(v);
        }
        return dies;
    }

    // =========================================================================
    // Interference graph
    // =========================================================================
    static Map<String,Set<String>> buildIG(List<Instruction> instrs, Liveness lv,
                                            List<Identifier> params) {
        Map<String,Set<String>> g = new LinkedHashMap<>();
        java.util.function.Consumer<String> node =
            v -> g.computeIfAbsent(v, k -> new LinkedHashSet<>());
        java.util.function.BiConsumer<String,String> edge = (a,b) -> {
            if (!a.equals(b)) {
                g.computeIfAbsent(a, k -> new LinkedHashSet<>()).add(b);
                g.computeIfAbsent(b, k -> new LinkedHashSet<>()).add(a);
            }
        };
        for (Identifier p : params) node.accept(p.toString());
        for (int i = 0; i < instrs.size(); i++) {
            for (String v : lv.def.get(i)) node.accept(v);
            for (String v : lv.use.get(i)) node.accept(v);
        }
        // params interfere with each other
        List<String> pl = new ArrayList<>();
        for (Identifier p : params) pl.add(p.toString());
        for (int a = 0; a < pl.size(); a++)
            for (int b = a+1; b < pl.size(); b++)
                edge.accept(pl.get(a), pl.get(b));
        // def interferes with liveOut; for moves, skip rhs (enables coalescing)
        for (int i = 0; i < instrs.size(); i++) {
            String mvRhs = (instrs.get(i) instanceof Move_Id_Id)
                ? ((Move_Id_Id)instrs.get(i)).rhs.toString() : null;
            for (String d : lv.def.get(i))
                for (String o : lv.out.get(i))
                    if (!o.equals(mvRhs)) edge.accept(d, o);
            // liveOut pairwise
            List<String> lo = new ArrayList<>(lv.out.get(i));
            for (int a = 0; a < lo.size(); a++)
                for (int b = a+1; b < lo.size(); b++)
                    edge.accept(lo.get(a), lo.get(b));
        }
        return g;
    }

    // =========================================================================
    // M1: Conservative move coalescing preferences
    // =========================================================================
    static Map<String,String> coalescePrefs(List<Instruction> instrs,
                                             Map<String,Set<String>> g) {
        Map<String,String> pref = new LinkedHashMap<>();
        for (Instruction ins : instrs) {
            if (!(ins instanceof Move_Id_Id)) continue;
            Move_Id_Id m = (Move_Id_Id)ins;
            String x = m.lhs.toString(), y = m.rhs.toString();
            if (!g.getOrDefault(x, Collections.emptySet()).contains(y))
                pref.putIfAbsent(x, y);
        }
        return pref;
    }

    // =========================================================================
    // A2: Chordal coloring — MCS + reverse PEO greedy
    //     S2: spill cheapest (lowest cost) when pressure
    //     S3: loop-depth costs fed in
    //     M1: honor coalesce preferences
    // =========================================================================
    static Map<String,String> chordalColor(Map<String,Set<String>> g,
                                            Set<String> spanning,
                                            Set<String> diesAtCallArg,
                                            Map<String,String> pref,
                                            Map<String,Double> cost) {
        List<String> vars = new ArrayList<>(g.keySet());
        if (vars.isEmpty()) return new HashMap<>();

        // MCS ordering with S2/S3 tie-breaking
        Map<String,Integer> weight = new LinkedHashMap<>();
        for (String v : vars) weight.put(v, 0);
        Set<String> remaining = new LinkedHashSet<>(vars);
        List<String> peo = new ArrayList<>();

        while (!remaining.isEmpty()) {
            String best = null; int bestW = -1; double bestCost = Double.MAX_VALUE;
            for (String v : remaining) {
                int w = weight.getOrDefault(v, 0);
                double c = cost.getOrDefault(v, 0.0);
                // Prefer to process high-weight vars first
                // Among ties: process higher-cost vars first (so cheap ones color later = more choices)
                if (best == null || w > bestW || (w == bestW && c > bestCost)) {
                    best = v; bestW = w; bestCost = c;
                }
            }
            peo.add(best); remaining.remove(best);
            for (String nb : g.getOrDefault(best, Collections.emptySet()))
                if (remaining.contains(nb)) weight.merge(nb, 1, Integer::sum);
        }

        // Greedy coloring in reverse PEO
        Collections.reverse(peo);
        Map<String,String> color = new LinkedHashMap<>();

        for (String v : peo) {
            Set<String> used = new HashSet<>();
            for (String nb : g.getOrDefault(v, Collections.emptySet())) {
                String c = color.get(nb);
                if (c != null) used.add(c);
            }
            boolean span  = spanning.contains(v);
            boolean dies  = diesAtCallArg.contains(v) && !span;
            String assigned = null;

            // M1: try coalesce preference first
            String prefVar = pref.get(v);
            if (prefVar != null) {
                String pc = color.get(prefVar);
                if (pc != null && !used.contains(pc)) {
                    boolean sOk = CALLEE_S.contains(pc);
                    boolean tOk = CALLER_T.contains(pc);
                    if ((span && sOk) || (!span && (tOk || sOk)))
                        assigned = pc;
                }
            }

            if (assigned == null) {
                if (span) {
                    // Call-spanning: must be in s-reg to survive calls cheaply
                    for (String r : CALLEE_S) if (!used.contains(r)) { assigned = r; break; }
                    if (assigned == null)
                        for (String r : CALLER_T) if (!used.contains(r)) { assigned = r; break; }
                } else if (dies) {
                    // Dies at call arg: prefer t-reg but don't use s-reg
                    // (keeping it spilled = cheaper than forcing _a slot)
                    for (String r : CALLER_T) if (!used.contains(r)) { assigned = r; break; }
                    // no s-reg fallback — stay spilled if no t-reg available
                } else {
                    for (String r : CALLER_T) if (!used.contains(r)) { assigned = r; break; }
                    if (assigned == null)
                        for (String r : CALLEE_S) if (!used.contains(r)) { assigned = r; break; }
                }
            }
            color.put(v, assigned);
        }
        return color;
    }

    // =========================================================================
    // Function compilation
    // =========================================================================
    static void compileFunction(FunctionDecl fn, StringBuilder out) {
        List<Instruction> instrs = fn.block.instructions;
        Identifier retId = fn.block.return_id;
        List<Identifier> params = fn.formalParameters;
        String fname = fn.functionName.toString();
        String fsafe = fname.replaceAll("[^a-zA-Z0-9_]", "_");

        // P2
        instrs = dce(instrs, params, retId);
        // P1
        Map<String,Instruction> remat = findRemat(instrs, params);
        // F1
        Liveness lv = liveness(instrs, params, retId);
        // C2 spanning (liveIn ∩ liveOut, remat excluded)
        Set<String> spanning = callSpanning(instrs, lv, remat);
        // diesAtCallArg classification
        Set<String> dies = findDiesAtCallArg(instrs, lv);
        // S3
        Map<String,Double> cost = spillCosts(instrs);
        // Interference graph
        Map<String,Set<String>> g = buildIG(instrs, lv, params);
        // M1 preferences
        Map<String,String> pref = coalescePrefs(instrs, g);
        // A2 coloring
        Map<String,String> regMap = chordalColor(g, spanning, dies, pref, cost);

        // C3: collect used s-regs
        Set<String> usedS = new LinkedHashSet<>();
        for (Map.Entry<String,String> e : regMap.entrySet())
            if (e.getValue() != null && CALLEE_S.contains(e.getValue()))
                usedS.add(e.getValue());
        List<String> slist = new ArrayList<>(usedS);

        // Emit header
        out.append("func ").append(fname).append("(");
        for (int i = 0; i < params.size(); i++) {
            if (i > 0) out.append(" ");
            out.append(params.get(i));
        }
        out.append(")\n");

        // C2 prologue: plain identifier saves (NO heap frame / alloc)
        // Each invocation gets its own activation record automatically — recursion safe.
        String savePrefix = "_sv_" + fsafe + "_";
        for (String sr : slist)
            out.append("  ").append(savePrefix).append(sr)
               .append(" = ").append(sr).append("\n");

        // Load params into registers
        for (Identifier p : params) {
            String reg = regMap.get(p.toString());
            if (reg != null)
                out.append("  ").append(reg).append(" = ").append(p).append("\n");
        }

        // Emit instructions
        for (int i = 0; i < instrs.size(); i++)
            emitInstr(instrs.get(i), regMap, lv.out.get(i), savePrefix, slist, remat, out);

        // Epilogue
        String retName = retId != null ? retId.toString() : T0;
        String retReg  = regMap.get(retName);

        // If return value is in an s-reg we're about to restore, presave it
        if (retReg != null && slist.contains(retReg)) {
            out.append("  ").append(retName).append(" = ").append(retReg).append("\n");
            retReg = null;
        }

        // Restore s-regs from plain identifier slots
        for (String sr : slist)
            out.append("  ").append(sr).append(" = ")
               .append(savePrefix).append(sr).append("\n");

        if (retReg != null)
            out.append("  ").append(retName).append(" = ").append(retReg).append("\n");
        out.append("  return ").append(retName).append("\n\n");
    }

    // =========================================================================
    // Emission helpers
    // =========================================================================
    static String useReg(String var, String scratch, Map<String,String> regMap,
                          Map<String,Instruction> remat, StringBuilder out) {
        String r = regMap.get(var);
        if (r != null) return r;
        Instruction ri = remat.get(var);
        if (ri != null) { emitRemat(ri, scratch, out); return scratch; }
        out.append("  ").append(scratch).append(" = ").append(var).append("\n");
        return scratch;
    }

    static String defReg(String var, String scratch, Map<String,String> regMap) {
        String r = regMap.get(var);
        return r != null ? r : scratch;
    }

    static void spill(String var, String scratch, Map<String,String> regMap,
                       Map<String,Instruction> remat, StringBuilder out) {
        if (regMap.get(var) == null && !remat.containsKey(var))
            out.append("  ").append(var).append(" = ").append(scratch).append("\n");
    }

    static void emitRemat(Instruction ins, String dest, StringBuilder out) {
        if (ins instanceof Move_Id_Integer)
            out.append("  ").append(dest).append(" = ")
               .append(((Move_Id_Integer)ins).rhs).append("\n");
        else if (ins instanceof Move_Id_FuncName)
            out.append("  ").append(dest).append(" = @")
               .append(((Move_Id_FuncName)ins).rhs).append("\n");
    }

    static void emitInstr(Instruction ins, Map<String,String> regMap,
                           Set<String> liveOut, String savePrefix,
                           List<String> slist, Map<String,Instruction> remat,
                           StringBuilder out) {
        if (ins instanceof LabelInstr) {
            out.append("  ").append(((LabelInstr)ins).label).append(":\n");

        } else if (ins instanceof Move_Id_Integer) {
            Move_Id_Integer m = (Move_Id_Integer)ins; String lhs = m.lhs.toString();
            if (remat.containsKey(lhs) && regMap.get(lhs) == null) return; // P1: skip spilled remat
            String r = defReg(lhs, T0, regMap);
            out.append("  ").append(r).append(" = ").append(m.rhs).append("\n");
            spill(lhs, r, regMap, remat, out);

        } else if (ins instanceof Move_Id_FuncName) {
            Move_Id_FuncName m = (Move_Id_FuncName)ins; String lhs = m.lhs.toString();
            if (remat.containsKey(lhs) && regMap.get(lhs) == null) return;
            String r = defReg(lhs, T0, regMap);
            out.append("  ").append(r).append(" = @").append(m.rhs).append("\n");
            spill(lhs, r, regMap, remat, out);

        } else if (ins instanceof Move_Id_Id) {
            Move_Id_Id m = (Move_Id_Id)ins;
            String lr = regMap.get(m.lhs.toString()), rr = regMap.get(m.rhs.toString());
            if (lr != null && lr.equals(rr)) return; // M1: coalesced away
            String rhs = useReg(m.rhs.toString(), T1, regMap, remat, out);
            String lhs = m.lhs.toString(); String r = defReg(lhs, T0, regMap);
            out.append("  ").append(r).append(" = ").append(rhs).append("\n");
            spill(lhs, r, regMap, remat, out);

        } else if (ins instanceof Add) {
            Add a = (Add)ins;
            String r1 = useReg(a.arg1.toString(), T0, regMap, remat, out);
            String r2 = useReg(a.arg2.toString(), T1, regMap, remat, out);
            String lhs = a.lhs.toString(); String r = defReg(lhs, T0, regMap);
            out.append("  ").append(r).append(" = ").append(r1).append(" + ").append(r2).append("\n");
            spill(lhs, r, regMap, remat, out);

        } else if (ins instanceof Subtract) {
            Subtract s = (Subtract)ins;
            String r1 = useReg(s.arg1.toString(), T0, regMap, remat, out);
            String r2 = useReg(s.arg2.toString(), T1, regMap, remat, out);
            String lhs = s.lhs.toString(); String r = defReg(lhs, T0, regMap);
            out.append("  ").append(r).append(" = ").append(r1).append(" - ").append(r2).append("\n");
            spill(lhs, r, regMap, remat, out);

        } else if (ins instanceof Multiply) {
            Multiply m = (Multiply)ins;
            String r1 = useReg(m.arg1.toString(), T0, regMap, remat, out);
            String r2 = useReg(m.arg2.toString(), T1, regMap, remat, out);
            String lhs = m.lhs.toString(); String r = defReg(lhs, T0, regMap);
            out.append("  ").append(r).append(" = ").append(r1).append(" * ").append(r2).append("\n");
            spill(lhs, r, regMap, remat, out);

        } else if (ins instanceof LessThan) {
            LessThan lt = (LessThan)ins;
            String r1 = useReg(lt.arg1.toString(), T0, regMap, remat, out);
            String r2 = useReg(lt.arg2.toString(), T1, regMap, remat, out);
            String lhs = lt.lhs.toString(); String r = defReg(lhs, T0, regMap);
            out.append("  ").append(r).append(" = ").append(r1).append(" < ").append(r2).append("\n");
            spill(lhs, r, regMap, remat, out);

        } else if (ins instanceof Load) {
            Load l = (Load)ins;
            String base = useReg(l.base.toString(), T1, regMap, remat, out);
            String lhs = l.lhs.toString(); String r = defReg(lhs, T0, regMap);
            out.append("  ").append(r).append(" = [").append(base).append("+").append(l.offset).append("]\n");
            spill(lhs, r, regMap, remat, out);

        } else if (ins instanceof Store) {
            Store s = (Store)ins;
            String base = useReg(s.base.toString(), T0, regMap, remat, out);
            String rhs  = useReg(s.rhs.toString(),  T1, regMap, remat, out);
            out.append("  [").append(base).append("+").append(s.offset).append("] = ").append(rhs).append("\n");

        } else if (ins instanceof Alloc) {
            Alloc a = (Alloc)ins;
            String size = useReg(a.size.toString(), T1, regMap, remat, out);
            String lhs = a.lhs.toString(); String r = defReg(lhs, T0, regMap);
            out.append("  ").append(r).append(" = alloc(").append(size).append(")\n");
            spill(lhs, r, regMap, remat, out);

        } else if (ins instanceof Print) {
            String r = useReg(((Print)ins).content.toString(), T0, regMap, remat, out);
            out.append("  print(").append(r).append(")\n");

        } else if (ins instanceof ErrorMessage) {
            out.append("  error(").append(((ErrorMessage)ins).msg).append(")\n");

        } else if (ins instanceof sparrow.Goto) {
            out.append("  goto ").append(((sparrow.Goto)ins).label).append("\n");

        } else if (ins instanceof IfGoto) {
            IfGoto ig = (IfGoto)ins;
            String r = useReg(ig.condition.toString(), T0, regMap, remat, out);
            out.append("  if0 ").append(r).append(" goto ").append(ig.label).append("\n");

        } else if (ins instanceof Call) {
            emitCall((Call)ins, regMap, liveOut, savePrefix, slist, remat, out);
        }
    }

    // =========================================================================
    // Call emission — C4 + arg setup
    // =========================================================================
    static void emitCall(Call c, Map<String,String> regMap, Set<String> liveOut,
                          String savePrefix, List<String> slist,
                          Map<String,Instruction> remat, StringBuilder out) {
        String lhs    = c.lhs.toString();
        String lhsReg = defReg(lhs, T0, regMap);
        int id = uid++;

        // C4: Save LIVE t-regs
        Map<String,String> saved = new LinkedHashMap<>();
        for (String v : liveOut) {
            if (v.equals(lhs)) continue;
            String r = regMap.get(v);
            if (r != null && CALLER_T.contains(r) && !saved.containsKey(r))
                saved.put(r, "_ct_" + id + "_" + r);
        }
        for (Map.Entry<String,String> e : saved.entrySet())
            out.append("  ").append(e.getValue()).append(" = ").append(e.getKey()).append("\n");

        // Load callee after saves
        String calleeReg = useReg(c.callee.toString(), T1, regMap, remat, out);

        // Build arg list:
        // - spilled identifiers: pass directly (zero cost)
        // - remat vars: rematerialize into slot
        // - register vars: copy to identifier slot
        List<String> argNames = new ArrayList<>();
        for (int i = 0; i < c.args.size(); i++) {
            String aname = c.args.get(i).toString();
            String areg  = regMap.get(aname);
            if (areg == null && !remat.containsKey(aname)) {
                // Already a spilled identifier — pass directly, zero cost!
                argNames.add(aname);
            } else {
                String slot = "_ca_" + id + "_" + i;
                if (areg != null) {
                    out.append("  ").append(slot).append(" = ").append(areg).append("\n");
                } else {
                    emitRemat(remat.get(aname), T0, out);
                    out.append("  ").append(slot).append(" = ").append(T0).append("\n");
                }
                argNames.add(slot);
            }
        }

        out.append("  ").append(lhsReg).append(" = call ").append(calleeReg).append("(");
        for (int i = 0; i < argNames.size(); i++) {
            if (i > 0) out.append(" ");
            out.append(argNames.get(i));
        }
        out.append(")\n");
        spill(lhs, lhsReg, regMap, remat, out);

        // Restore saved t-regs
        for (Map.Entry<String,String> e : saved.entrySet())
            if (!e.getKey().equals(lhsReg))
                out.append("  ").append(e.getKey()).append(" = ").append(e.getValue()).append("\n");
    }
}