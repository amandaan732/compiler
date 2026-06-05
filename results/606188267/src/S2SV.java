import sparrow.*;
import sparrow.visitor.ArgVisitor;
import IR.SparrowParser;
import IR.visitor.SparrowConstructor;
import IR.token.Identifier;
import IR.token.Label;
import IR.token.Register;

import java.util.*;


public class S2SV {

    static final String SCRATCH1 = "t0";
    static final String SCRATCH2 = "t1";

    // static final List<String> CALLER_T = Arrays.asList("t2","t3","t4","t5");
    static final List<String> CALLER_T = Arrays.asList("t2","t3","t4","t5","a2","a3","a4","a5","a6","a7");
    static final List<String> CALLEE_S = Arrays.asList("s1","s2","s3","s4","s5","s6","s7","s8","s9","s10","s11");
    static int callSiteId = 0;

    public static void main(String[] args) throws Exception {
        new SparrowParser(System.in);
        IR.syntaxtree.Program syntaxTree = SparrowParser.Program();
        SparrowConstructor constructor = new SparrowConstructor();
        syntaxTree.accept(constructor);
        sparrow.Program prog = constructor.getProgram();


        StringBuilder sb = new StringBuilder();
        for (FunctionDecl func : prog.funDecls) {
            compileFunction(func, sb);
        }

        System.out.print(sb);
    }


    static class LivenessResult {
        List<Set<String>> liveIn, liveOut, def, use;
    }

    static LivenessResult computeLiveness(List<Instruction> instrs, List<Identifier> params, Identifier retId) {
        int n = instrs.size();
        List<Set<String>> def = new ArrayList<>(), use = new ArrayList<>();
        List<Set<String>> liveIn = new ArrayList<>(), liveOut = new ArrayList<>();

        Map<String, Integer> labelIndex = new HashMap<>();
        for (int i = 0; i < n; i++) {
            if (instrs.get(i) instanceof LabelInstr) {
                labelIndex.put(((LabelInstr)instrs.get(i)).label.toString(), i);
            }
            Set<String> d = new HashSet<>(), u = new HashSet<>();
            instrDefUse(instrs.get(i), d, u);
            def.add(d); 
            use.add(u);
            liveIn.add(new HashSet<>()); 
            liveOut.add(new HashSet<>());
        }

        Set<String> retSet = new HashSet<>();
        if (retId != null) {
            retSet.add(retId.toString());
        }

        boolean changed = true;
        while (changed) {
            changed = false;
            for (int i = n - 1; i >= 0; i--) {
                Set<String> newOut = new HashSet<>();
                Instruction ins = instrs.get(i);
                if (ins instanceof sparrow.Goto) {
                    Integer idx = labelIndex.get(((sparrow.Goto)ins).label.toString());
                    if (idx != null) {
                        newOut.addAll(liveIn.get(idx));
                    }
                } 
                else if (ins instanceof IfGoto) {
                    Integer idx = labelIndex.get(((IfGoto)ins).label.toString());
                    if (idx != null) {
                        newOut.addAll(liveIn.get(idx));
                    }
                    if (i + 1 < n) {
                        newOut.addAll(liveIn.get(i + 1));
                    }
                } 
                else {
                    if (i + 1 < n) {
                        newOut.addAll(liveIn.get(i + 1));
                    }
                    else newOut.addAll(retSet);
                }
                if (i == n - 1) {
                    newOut.addAll(retSet);
                }

                Set<String> newIn = new HashSet<>(use.get(i));
                Set<String> tmp = new HashSet<>(newOut); 
                tmp.removeAll(def.get(i));
                newIn.addAll(tmp);
                if (!newOut.equals(liveOut.get(i)) || !newIn.equals(liveIn.get(i))) {
                    liveOut.set(i, newOut); liveIn.set(i, newIn); 
                    changed = true;
                }
            }
        }
        LivenessResult res = new LivenessResult();
        res.def = def; 
        res.use = use; 
        res.liveIn = liveIn; 
        res.liveOut = liveOut;
        return res;
    }

    static void instrDefUse(Instruction ins, Set<String> def, Set<String> use) {
        if (ins instanceof Move_Id_Integer) { 
            def.add(((Move_Id_Integer)ins).lhs.toString()); 
        }
        else if (ins instanceof Move_Id_FuncName) { 
            def.add(((Move_Id_FuncName)ins).lhs.toString()); 
        }
        else if (ins instanceof Move_Id_Id) { 
            Move_Id_Id m=(Move_Id_Id)ins; def.add(m.lhs.toString()); use.add(m.rhs.toString()); 
        }
        else if (ins instanceof Add) { 
            Add a=(Add)ins; def.add(a.lhs.toString()); use.add(a.arg1.toString()); use.add(a.arg2.toString()); 
        }

        else if (ins instanceof Subtract) { 
            Subtract s=(Subtract)ins; def.add(s.lhs.toString()); use.add(s.arg1.toString()); use.add(s.arg2.toString()); 
        }
        else if (ins instanceof Multiply) { 
            Multiply m=(Multiply)ins; def.add(m.lhs.toString()); use.add(m.arg1.toString()); use.add(m.arg2.toString()); 
        }
        else if (ins instanceof LessThan) { 
            LessThan l=(LessThan)ins; def.add(l.lhs.toString()); use.add(l.arg1.toString()); use.add(l.arg2.toString()); 
        }
        else if (ins instanceof Load) { 
            Load l=(Load)ins; def.add(l.lhs.toString()); use.add(l.base.toString()); 
        }
        else if (ins instanceof Store) { 
            Store s=(Store)ins; use.add(s.base.toString()); use.add(s.rhs.toString()); 
        }
        else if (ins instanceof Alloc) { 
            Alloc a=(Alloc)ins; def.add(a.lhs.toString()); use.add(a.size.toString()); 
        }
        else if (ins instanceof Print) { 
            use.add(((Print)ins).content.toString()); 
        }
        else if (ins instanceof IfGoto) { 
            use.add(((IfGoto)ins).condition.toString()); 
        }
        else if (ins instanceof Call) {
            Call c=(Call)ins; def.add(c.lhs.toString()); use.add(c.callee.toString());
            for (Identifier a : c.args) {
                use.add(a.toString());
            }
        }
    }

    static Set<String> findCallSpanning(List<Instruction> instrs, LivenessResult lv) {
        Set<String> spanning = new HashSet<>();
        for (int i = 0; i < instrs.size(); i++) {
            if (instrs.get(i) instanceof Call) {
                spanning.addAll(lv.liveOut.get(i));
            }
        }
        return spanning;
    }

    static Map<String, Set<String>> buildInterferenceGraph(List<Instruction> instrs, LivenessResult lv, List<Identifier> params, Identifier retId) {
        Map<String, Set<String>> graph = new LinkedHashMap<>();
        java.util.function.Consumer<String> addNode = v -> graph.computeIfAbsent(v, k -> new LinkedHashSet<>());
        for (Identifier p : params) {
            addNode.accept(p.toString());
        }
        if (retId != null) {
            addNode.accept(retId.toString());
        }
        for (int i = 0; i < instrs.size(); i++) {
            for (String v : lv.def.get(i)) {
                addNode.accept(v);
            }
            for (String v : lv.use.get(i)) {
                addNode.accept(v);
            }
        }

        java.util.function.BiConsumer<String, String> addEdge = (a, b) -> {
            if (!a.equals(b)) {
                graph.computeIfAbsent(a, k -> new LinkedHashSet<>()).add(b);
                graph.computeIfAbsent(b, k -> new LinkedHashSet<>()).add(a);
            }
        };

        List<String> pnames = new ArrayList<>();
        for (Identifier p : params) {
            pnames.add(p.toString());
        }
        for (int a = 0; a < pnames.size(); a++) {
            for (int b = a+1; b < pnames.size(); b++) {
                addEdge.accept(pnames.get(a), pnames.get(b));
            }
        }
        for (int i = 0; i < instrs.size(); i++) {
            List<String> lout = new ArrayList<>(lv.liveOut.get(i));
            for (int a = 0; a < lout.size(); a++) {
                for (int b = a+1; b < lout.size(); b++) {
                    addEdge.accept(lout.get(a), lout.get(b));
                }
            }
            for (String d : lv.def.get(i)) {
                for (String o : lv.liveOut.get(i)) {
                    addEdge.accept(d, o);
                }
            }
        }
        return graph;
    }

    static Map<String, String> chordalColor(Map<String, Set<String>> graph, Set<String> spanning) {
        List<String> vars = new ArrayList<>(graph.keySet());
        if (vars.isEmpty()) {
            return new HashMap<>();
        }

        Map<String, Integer> weight = new LinkedHashMap<>();
        for (String v : vars) {
            weight.put(v, 0);
        }
        List<String> peo = new ArrayList<>();
        Set<String> remaining = new LinkedHashSet<>(vars);
        for (int i = vars.size() - 1; i >= 0; i--) {
            String best = null; int bestW = -1;
            for (String v : remaining) {
                int w = weight.getOrDefault(v, 0);
                if (w > bestW) { bestW = w; best = v; }
            }
            peo.add(best); remaining.remove(best);
            for (String nb : graph.getOrDefault(best, Collections.emptySet())) {
                if (remaining.contains(nb)) {
                    weight.merge(nb, 1, Integer::sum);
                }
            }
        }


        Map<String, String> coloring = new HashMap<>();
        Collections.reverse(peo);
        for (String v : peo) {
            Set<String> used = new HashSet<>();
            for (String nb : graph.getOrDefault(v, Collections.emptySet())) {
                String c = coloring.get(nb);
                if (c != null) {
                    used.add(c);
                }
            }
            boolean span = spanning.contains(v);
            String assigned = null;
            if (span) {
                for (String r : CALLEE_S) if (!used.contains(r)) { assigned = r; break; }
                //if no s-reg available, spill to identifier; never use t-reg for spanning vars
                //t-regs in spanning position in loops == need save/restore at every call site
            } 
            else {
                for (String r : CALLER_T) if (!used.contains(r)) { 
                    assigned = r; break; 
                }
                if (assigned == null) {
                    for (String r : CALLEE_S) {
                        if (!used.contains(r)) { 
                            assigned = r; break; 
                        }
                    }
                }
            }
            coloring.put(v, assigned);
        }
        return coloring;
    }

    static void compileFunction(FunctionDecl func, StringBuilder out) {
        List<Instruction> instrs = func.block.instructions;
        Identifier retId = func.block.return_id;
        List<Identifier> params = func.formalParameters;
        String fname = func.functionName.toString();
        String fsafe = fname.replaceAll("[^a-zA-Z0-9]", "_"); //sani. fn name to use in id

        LivenessResult lv = computeLiveness(instrs, params, retId);
        Set<String> spanning = findCallSpanning(instrs, lv);
        Map<String, Set<String>> graph = buildInterferenceGraph(instrs, lv, params, retId);
        Map<String, String> regMap = chordalColor(graph, spanning);

        //find used s-regs (only save used ones)
        Set<String> usedSRegs = new LinkedHashSet<>();
        for (String reg : regMap.values()) {
            if (reg != null && CALLEE_S.contains(reg)) {
                usedSRegs.add(reg);
            }
        }
        List<String> usedSList = new ArrayList<>(usedSRegs);

        out.append("func ").append(fname).append("(");
        for (int i = 0; i < params.size(); i++) {
            if (i > 0) {
                out.append(" ");
            }
            out.append(params.get(i));
        }
        out.append(")\n");

        //alloc heap frame
            //save used s-regs
        String frameVar = null;
        if (!usedSList.isEmpty()) {
            frameVar = "_fr_" + fsafe;
            int frameSize = usedSList.size() * 4;
            out.append("  ").append(SCRATCH1).append(" = ").append(frameSize).append("\n");
            out.append("  ").append(SCRATCH1).append(" = alloc(").append(SCRATCH1).append(")\n");
            out.append("  ").append(frameVar).append(" = ").append(SCRATCH1).append("\n");
            for (int i = 0; i < usedSList.size(); i++) {
                out.append("  [").append(SCRATCH1).append("+").append(i*4).append("] = ").append(usedSList.get(i)).append("\n");
            }
        }

        //load params into regs
        for (Identifier p : params) {
            String reg = regMap.get(p.toString());
            if (reg != null) {
                out.append("  ").append(reg).append(" = ").append(p).append("\n");
            }
        }

        for (int i = 0; i < instrs.size(); i++) {
            emitInstruction(instrs.get(i), regMap, lv.liveOut.get(i), frameVar, usedSList, fsafe, out);
        }

        String retName = retId != null ? retId.toString() : SCRATCH1;
        String retReg = regMap.get(retName);

        //if ret val == in s-reg 
            //epilogue == restore (clobber); save it first
        boolean retNeedsPresave = (frameVar != null && retReg != null && usedSList.contains(retReg));
        if (retNeedsPresave) {
            out.append("  ").append(retName).append(" = ").append(retReg).append("\n");
        }

        //epi; restore s-regs from heap frame
        if (frameVar != null) {
            out.append("  ").append(SCRATCH1).append(" = ").append(frameVar).append("\n");
            for (int i = 0; i < usedSList.size(); i++) {
                out.append("  ").append(usedSList.get(i)).append(" = [").append(SCRATCH1).append("+").append(i*4).append("]\n");
            }
        }

        if (!retNeedsPresave && retReg != null) {
            out.append("  ").append(retName).append(" = ").append(retReg).append("\n");
        }
        out.append("  return ").append(retName).append("\n\n");
    }

    static String useReg(String var, String scratch, Map<String, String> regMap, StringBuilder out) {
        String reg = regMap.get(var);
        if (reg != null) {
            return reg;
        }
        out.append("  ").append(scratch).append(" = ").append(var).append("\n");
        return scratch;
    }

    static String defReg(String var, String scratch, Map<String, String> regMap) {
        String reg = regMap.get(var);
        return reg != null ? reg : scratch;
    }

    static void storeSpill(String var, String scratch, Map<String, String> regMap, StringBuilder out) {
        if (regMap.get(var) == null) {
            out.append("  ").append(var).append(" = ").append(scratch).append("\n");
        }
    }

    static void emitInstruction(Instruction ins,Map<String, String> regMap, Set<String> liveOut, String frameVar, List<String> usedSList, String fsafe, StringBuilder out) {
        if (ins instanceof LabelInstr) {
            out.append("  ").append(((LabelInstr)ins).label).append(":\n");
        } 
        else if (ins instanceof Move_Id_Integer) {
            Move_Id_Integer m = (Move_Id_Integer)ins; String lhs = m.lhs.toString();
            String r = defReg(lhs, SCRATCH1, regMap);
            out.append("  ").append(r).append(" = ").append(m.rhs).append("\n");
            storeSpill(lhs, r, regMap, out);
        } 
        else if (ins instanceof Move_Id_FuncName) {
            Move_Id_FuncName m = (Move_Id_FuncName)ins; String lhs = m.lhs.toString();
            String r = defReg(lhs, SCRATCH1, regMap);
            out.append("  ").append(r).append(" = @").append(m.rhs).append("\n");
            storeSpill(lhs, r, regMap, out);
        } 
        else if (ins instanceof Move_Id_Id) {
            Move_Id_Id m = (Move_Id_Id)ins;
            String rhs = useReg(m.rhs.toString(), SCRATCH2, regMap, out);
            String lhs = m.lhs.toString(); 
            String r = defReg(lhs, SCRATCH1, regMap);
            out.append("  ").append(r).append(" = ").append(rhs).append("\n");
            storeSpill(lhs, r, regMap, out);
        } 
        else if (ins instanceof Add) {
            Add a = (Add)ins;
            String r1 = useReg(a.arg1.toString(), SCRATCH1, regMap, out);
            String r2 = useReg(a.arg2.toString(), SCRATCH2, regMap, out);
            String lhs = a.lhs.toString(); 
            String r = defReg(lhs, SCRATCH1, regMap);
            out.append("  ").append(r).append(" = ").append(r1).append(" + ").append(r2).append("\n");
            storeSpill(lhs, r, regMap, out);
        } 
        else if (ins instanceof Subtract) {
            Subtract s = (Subtract)ins;
            String r1 = useReg(s.arg1.toString(), SCRATCH1, regMap, out);
            String r2 = useReg(s.arg2.toString(), SCRATCH2, regMap, out);
            String lhs = s.lhs.toString(); 
            String r = defReg(lhs, SCRATCH1, regMap);
            out.append("  ").append(r).append(" = ").append(r1).append(" - ").append(r2).append("\n");
            storeSpill(lhs, r, regMap, out);
        } 
        else if (ins instanceof Multiply) {
            Multiply m = (Multiply)ins;
            String r1 = useReg(m.arg1.toString(), SCRATCH1, regMap, out);
            String r2 = useReg(m.arg2.toString(), SCRATCH2, regMap, out);
            String lhs = m.lhs.toString(); 
            String r = defReg(lhs, SCRATCH1, regMap);
            out.append("  ").append(r).append(" = ").append(r1).append(" * ").append(r2).append("\n");
            storeSpill(lhs, r, regMap, out);
        } 
        else if (ins instanceof LessThan) {
            LessThan lt =(LessThan)ins;
            String r1 = useReg(lt.arg1.toString(), SCRATCH1, regMap, out);
            String r2 = useReg(lt.arg2.toString(), SCRATCH2, regMap, out);
            String lhs = lt.lhs.toString(); 
            String r = defReg(lhs, SCRATCH1, regMap);
            out.append("  ").append(r).append(" = ").append(r1).append(" < ").append(r2).append("\n");
            storeSpill(lhs, r, regMap, out);
        } 
        else if (ins instanceof Load) {
            Load l = (Load)ins;
            String base = useReg(l.base.toString(), SCRATCH2, regMap, out);
            String lhs = l.lhs.toString(); 
            String r = defReg(lhs, SCRATCH1, regMap);
            out.append("  ").append(r).append(" = [").append(base).append("+").append(l.offset).append("]\n");
            storeSpill(lhs, r, regMap, out);
        } 
        else if (ins instanceof Store) {
            Store s = (Store)ins;
            String base = useReg(s.base.toString(), SCRATCH1, regMap, out);
            String rhs = useReg(s.rhs.toString(), SCRATCH2, regMap, out);
            out.append("  [").append(base).append("+").append(s.offset).append("] = ").append(rhs).append("\n");
        } 
        else if (ins instanceof Alloc) {
            Alloc a = (Alloc)ins;
            String size = useReg(a.size.toString(), SCRATCH2, regMap, out);
            String lhs = a.lhs.toString(); 
            String r = defReg(lhs, SCRATCH1, regMap);
            out.append("  ").append(r).append(" = alloc(").append(size).append(")\n");
            storeSpill(lhs, r, regMap, out);
        } 
        else if (ins instanceof Print) {
            String r = useReg(((Print)ins).content.toString(), SCRATCH1, regMap, out);
            out.append("  print(").append(r).append(")\n");
        } 
        else if (ins instanceof ErrorMessage) {
            out.append("  error(").append(((ErrorMessage)ins).msg).append(")\n");
        } 
        else if (ins instanceof sparrow.Goto) {
            out.append("  goto ").append(((sparrow.Goto)ins).label).append("\n");
        } 
        else if (ins instanceof IfGoto) {
            IfGoto ig = (IfGoto)ins;
            String r = useReg(ig.condition.toString(), SCRATCH1, regMap, out);
            out.append("  if0 ").append(r).append(" goto ").append(ig.label).append("\n");
        } 
        else if (ins instanceof Call) {
            emitCall((Call)ins, regMap, liveOut, frameVar, usedSList, fsafe, out);
        }
    }

    static void emitCall(Call c, Map<String, String> regMap, Set<String> liveOut,
                          String frameVar, List<String> usedSList, String fsafe, StringBuilder out) {
        String lhs = c.lhs.toString();
        String lhsReg = defReg(lhs, SCRATCH1, regMap);
        String callee = useReg(c.callee.toString(), SCRATCH2, regMap, out);
        int sid = callSiteId++;

        //save only LIVE t-regs across this call --> s-regs preserved by callee
            //key: deduplicate by register + collect vars
            //map from reg -> save slot name
        Map<String, String> tRegSaveSlot = new LinkedHashMap<>();
        for (String v : liveOut) {
            if (v.equals(lhs)) {
                continue;
            }

            String reg = regMap.get(v);
            if (reg != null && CALLER_T.contains(reg) && !tRegSaveSlot.containsKey(reg)) {
                String slot = "_t" + sid + "_" + reg;
                tRegSaveSlot.put(reg, slot);
            }
        }

        //save live t-regs
        for (Map.Entry<String, String> e : tRegSaveSlot.entrySet()) {
            out.append("  ").append(e.getValue()).append(" = ").append(e.getKey()).append("\n");
        }

        //build arg slots
            //Sparrow-V ==needs non-reg id as call args
        List<String> argSlots = new ArrayList<>();
        int idx = 0;
        for (Identifier arg : c.args) {
            String aname = arg.toString();
            String areg = regMap.get(aname);
            String slot = "_a" + sid + "x" + idx++;
            if (areg != null) {
                out.append("  ").append(slot).append(" = ").append(areg).append("\n");
            } 
            else {
                out.append("  ").append(SCRATCH1).append(" = ").append(aname).append("\n");
                out.append("  ").append(slot).append(" = ").append(SCRATCH1).append("\n");
            }
            argSlots.add(slot);
        }

        out.append("  ").append(lhsReg).append(" = call ").append(callee).append("(");
        for (int i = 0; i < argSlots.size(); i++) {
            if (i > 0) out.append(" ");
            out.append(argSlots.get(i));
        }
        out.append(")\n");
        storeSpill(lhs, lhsReg, regMap, out);

        //restore live t-regs (skip lhsReg --> it holds call result)
        for (Map.Entry<String, String> e : tRegSaveSlot.entrySet()) {
            if (!e.getKey().equals(lhsReg)) {
                out.append("  ").append(e.getKey()).append(" = ").append(e.getValue()).append("\n");
            }
        }
        //s-regs != saved/restored here (the callee preserves them w/ own prologue/epilogue heap frame)
    }
}
