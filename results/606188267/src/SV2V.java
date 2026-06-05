import sparrowv.*;
import sparrowv.visitor.*;
import IR.SparrowParser;
import IR.visitor.SparrowVConstructor;
import IR.token.Identifier;
import IR.token.Register;
import IR.token.FunctionName;

import java.util.*;

/**
 * SV2V: Sparrow-V -> RISC-V
 *
 * Ecall conventions (Venus/MARS):
 *   a0 = syscall number, a1 = argument
 *   1  = print_int (a1 = integer)
 *   11 = print_char (a1 = char)
 *   9  = sbrk/alloc (a1 = size, returns address in a0)
 *   10 = exit
 *
 * Frame layout (s0 = fp points to top of frame):
 *   [s0-4]  = saved ra
 *   [s0-8]  = saved s0 (caller fp)
 *   [s0-12] = local var 0
 *   [s0-16] = local var 1
 *   ...
 *
 * Args: a0-a7 for first 8, rest on stack
 * Return value: a0
 */
public class SV2V {

    public static void main(String[] args) throws Exception {
        new SparrowParser(System.in);
        IR.syntaxtree.Program syntaxTree = SparrowParser.Program();
        SparrowVConstructor ctor = new SparrowVConstructor();
        syntaxTree.accept(ctor);
        sparrowv.Program prog = ctor.getProgram();

        StringBuilder out = new StringBuilder();

        // Ecall aliases
        out.append("  .equiv @print_int, 1\n");
        out.append("  .equiv @print_char, 11\n");
        out.append("  .equiv @exit, 10\n");
        out.append("  .equiv @sbrk, 9\n");
        out.append("\n.data\n");
        out.append("_nl: .asciiz \"\\n\"\n");
        out.append("\n.text\n");
        out.append("  jal Main\n");
        out.append("  li a0, @exit\n");
        out.append("  ecall\n\n");

        // Alloc helper
        out.append("alloc:\n");
        out.append("  mv a1, a0\n");
        out.append("  li a0, @sbrk\n");
        out.append("  ecall\n");
        out.append("  jr ra\n\n");

        for (FunctionDecl fn : prog.funDecls) {
            compileFunction(fn, out);
        }

        System.out.print(out);
    }

    static void compileFunction(FunctionDecl fn, StringBuilder out) {
        String fname = fn.functionName.toString();
        List<Identifier> params = fn.formalParameters;
        List<Instruction> instrs = fn.block.instructions;
        Identifier retId = fn.block.return_id;

        // Collect all identifiers needing stack slots
        Set<String> idSet = new LinkedHashSet<>();
        for (Identifier p : params) idSet.add(p.toString());
        for (Instruction ins : instrs) collectIds(ins, idSet);
        if (retId != null) idSet.add(retId.toString());

        // Assign offsets from s0: -12, -16, ...
        Map<String, Integer> offsets = new LinkedHashMap<>();
        int off = -12;
        for (String id : idSet) {
            offsets.put(id, off);
            off -= 4;
        }

        // Frame size: ra(4) + old_s0(4) + locals
        int localsSize = idSet.size() * 4;
        int frameSize = 8 + localsSize;
        // Align to 16
        if (frameSize % 16 != 0) frameSize = ((frameSize / 16) + 1) * 16;

        out.append(fname).append(":\n");

        // Prologue
        out.append("  addi sp, sp, -").append(frameSize).append("\n");
        out.append("  sw ra, ").append(frameSize - 4).append("(sp)\n");
        out.append("  sw s0, ").append(frameSize - 8).append("(sp)\n");
        out.append("  addi s0, sp, ").append(frameSize).append("\n");

        // Store incoming args (a0-a7) into param slots
        String[] argRegs = {"a0","a1","a2","a3","a4","a5","a6","a7"};
        for (int i = 0; i < params.size() && i < 8; i++) {
            int poff = offsets.get(params.get(i).toString());
            out.append("  sw ").append(argRegs[i]).append(", ").append(poff).append("(s0)\n");
        }
        // Stack args (beyond 8): at positive offset from old sp = s0 - frameSize
        // Caller pushed them at sp+0, sp+4, ... before the call
        // They're at frameSize(sp) = 0(s0), frameSize+4(sp) = 4(s0)... actually
        // they're at the caller's sp level, which is our s0
        // So stack arg i (0-indexed beyond 8) is at (i*4)(s0) -- above our frame
        for (int i = 8; i < params.size(); i++) {
            int poff = offsets.get(params.get(i).toString());
            out.append("  lw t0, ").append((i - 8) * 4).append("(s0)\n");
            out.append("  sw t0, ").append(poff).append("(s0)\n");
        }

        // Emit instructions
        for (Instruction ins : instrs) {
            emitInstruction(ins, offsets, out);
        }

        // Epilogue: load return value into a0
        if (retId != null) {
            int roff = offsets.get(retId.toString());
            out.append("  lw a0, ").append(roff).append("(s0)\n");
        } else {
            out.append("  li a0, 0\n");
        }
        out.append("  lw ra, ").append(frameSize - 4).append("(sp)\n");
        out.append("  lw s0, ").append(frameSize - 8).append("(sp)\n");
        out.append("  addi sp, sp, ").append(frameSize).append("\n");
        out.append("  jr ra\n\n");
    }

    static void collectIds(Instruction ins, Set<String> ids) {
        if (ins instanceof Move_Id_Reg) {
            ids.add(((Move_Id_Reg)ins).lhs.toString());
        } else if (ins instanceof Move_Reg_Id) {
            ids.add(((Move_Reg_Id)ins).rhs.toString());
        } else if (ins instanceof Call) {
            Call c = (Call)ins;
            ids.add(c.lhs.toString());
            for (Identifier a : c.args) ids.add(a.toString());
        }
    }

    static void loadId(String id, String reg, Map<String, Integer> offsets, StringBuilder out) {
        Integer o = offsets.get(id);
        if (o != null) {
            out.append("  lw ").append(reg).append(", ").append(o).append("(s0)\n");
        } else {
            out.append("  li ").append(reg).append(", 0  # unknown id: ").append(id).append("\n");
        }
    }

    static void storeId(String id, String reg, Map<String, Integer> offsets, StringBuilder out) {
        Integer o = offsets.get(id);
        if (o != null) {
            out.append("  sw ").append(reg).append(", ").append(o).append("(s0)\n");
        }
    }

    static void emitInstruction(Instruction ins, Map<String, Integer> offsets, StringBuilder out) {
        if (ins instanceof LabelInstr) {
            out.append(((LabelInstr)ins).label).append(":\n");

        } else if (ins instanceof Move_Reg_Integer) {
            Move_Reg_Integer m = (Move_Reg_Integer)ins;
            out.append("  li ").append(m.lhs).append(", ").append(m.rhs).append("\n");

        } else if (ins instanceof Move_Reg_FuncName) {
            Move_Reg_FuncName m = (Move_Reg_FuncName)ins;
            out.append("  la ").append(m.lhs).append(", ").append(m.rhs).append("\n");

        } else if (ins instanceof Move_Reg_Reg) {
            Move_Reg_Reg m = (Move_Reg_Reg)ins;
            if (!m.lhs.toString().equals(m.rhs.toString()))
                out.append("  mv ").append(m.lhs).append(", ").append(m.rhs).append("\n");

        } else if (ins instanceof Move_Id_Reg) {
            Move_Id_Reg m = (Move_Id_Reg)ins;
            storeId(m.lhs.toString(), m.rhs.toString(), offsets, out);

        } else if (ins instanceof Move_Reg_Id) {
            Move_Reg_Id m = (Move_Reg_Id)ins;
            loadId(m.rhs.toString(), m.lhs.toString(), offsets, out);

        } else if (ins instanceof Add) {
            Add a = (Add)ins;
            out.append("  add ").append(a.lhs).append(", ").append(a.arg1).append(", ").append(a.arg2).append("\n");

        } else if (ins instanceof Subtract) {
            Subtract s = (Subtract)ins;
            out.append("  sub ").append(s.lhs).append(", ").append(s.arg1).append(", ").append(s.arg2).append("\n");

        } else if (ins instanceof Multiply) {
            Multiply m = (Multiply)ins;
            out.append("  mul ").append(m.lhs).append(", ").append(m.arg1).append(", ").append(m.arg2).append("\n");

        } else if (ins instanceof LessThan) {
            LessThan lt = (LessThan)ins;
            out.append("  slt ").append(lt.lhs).append(", ").append(lt.arg1).append(", ").append(lt.arg2).append("\n");

        } else if (ins instanceof Load) {
            Load l = (Load)ins;
            out.append("  lw ").append(l.lhs).append(", ").append(l.offset).append("(").append(l.base).append(")\n");

        } else if (ins instanceof Store) {
            Store s = (Store)ins;
            out.append("  sw ").append(s.rhs).append(", ").append(s.offset).append("(").append(s.base).append(")\n");

        } else if (ins instanceof Alloc) {
            Alloc a = (Alloc)ins;
            // Save ra around alloc call if needed
            out.append("  mv a0, ").append(a.size).append("\n");
            out.append("  jal alloc\n");
            out.append("  mv ").append(a.lhs).append(", a0\n");

        } else if (ins instanceof Print) {
            Print p = (Print)ins;
            out.append("  mv a1, ").append(p.content).append("\n");
            out.append("  li a0, @print_int\n");
            out.append("  ecall\n");
            // Print newline
            out.append("  li a1, 10\n");
            out.append("  li a0, @print_char\n");
            out.append("  ecall\n");

        } else if (ins instanceof ErrorMessage) {
            out.append("  li a0, @exit\n");
            out.append("  ecall\n");

        } else if (ins instanceof sparrowv.Goto) {
            out.append("  j ").append(((sparrowv.Goto)ins).label).append("\n");

        } else if (ins instanceof IfGoto) {
            IfGoto ig = (IfGoto)ins;
            out.append("  beqz ").append(ig.condition).append(", ").append(ig.label).append("\n");

        } else if (ins instanceof Call) {
            emitCall((Call)ins, offsets, out);
        }
    }

    static void emitCall(Call c, Map<String, Integer> offsets, StringBuilder out) {
        List<Identifier> args = c.args;
        String[] argRegs = {"a0","a1","a2","a3","a4","a5","a6","a7"};
        int stackArgs = Math.max(0, args.size() - 8);

        // Push extra stack args first (in reverse so arg8 is at lowest addr)
        if (stackArgs > 0) {
            out.append("  addi sp, sp, -").append(stackArgs * 4).append("\n");
            for (int i = args.size() - 1; i >= 8; i--) {
                loadId(args.get(i).toString(), "t0", offsets, out);
                out.append("  sw t0, ").append((i - 8) * 4).append("(sp)\n");
            }
        }

        // Load first 8 args into a0-a7
        // Must be careful: load all before storing any (use t0 as temp if needed)
        // Simple approach: load in order (works when args don't alias registers)
        for (int i = 0; i < args.size() && i < 8; i++) {
            loadId(args.get(i).toString(), argRegs[i], offsets, out);
        }

        // Call
        out.append("  jalr ").append(c.callee).append("\n");

        // Clean up stack args
        if (stackArgs > 0) {
            out.append("  addi sp, sp, ").append(stackArgs * 4).append("\n");
        }

        // Store return value (a0) into lhs
        storeId(c.lhs.toString(), "a0", offsets, out);
    }
}