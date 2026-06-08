import sparrowv.*;
import sparrowv.visitor.*;
import IR.SparrowParser;
import IR.visitor.SparrowVConstructor;
import IR.syntaxtree.Node;
import IR.token.Identifier;
import IR.token.Register;
import IR.token.FunctionName;
import IR.registers.Registers;
import java.io.InputStream;
import java.util.*;


public class SV2V {

    public static void main(String[] args) throws Exception {
        Registers.SetRiscVregs();
        InputStream in = System.in;
        new SparrowParser(in);

        Node root = SparrowParser.Program();
        SparrowVConstructor constructor = new SparrowVConstructor();
        root.accept(constructor);
        sparrowv.Program program = constructor.getProgram();


        StringBuilder out = new StringBuilder();

        //took from a TA note on piazza:
        out.append(".equiv @sbrk, 9\n");
        out.append(".equiv @print_string, 4\n");
        out.append(".equiv @print_char, 11\n");
        out.append(".equiv @print_int, 1\n");
        out.append(".equiv @exit, 10\n");
        out.append(".equiv @exit2, 17\n");
        String entryName = program.funDecls.get(0).functionName.toString();
        out.append(".text\n");
        out.append(".globl main\n");
        //if the user's entry function is also named "main"
            //the stub IS the fn
        //else
            //emit a stub that calls the user's entry then exits
        if (!entryName.equals("main")) {
            out.append("main:\n");
            out.append("  jal ").append(entryName).append("\n");
            out.append("  li a0, @exit\n");
            out.append("  ecall\n");
        }
        out.append(".globl print\n");
        out.append("print:\n");
        out.append("  mv a1, a0\n");
        out.append("  li a0, @print_int\n");
        out.append("  ecall\n");
        out.append("  li a1, 10\n");
        out.append("  li a0, @print_char\n");
        out.append("  ecall\n");
        out.append("  jr ra\n");
        out.append(".globl error\n");
        out.append("error:\n");
        out.append("  mv a1, a0\n");
        out.append("  li a0, @print_string\n");
        out.append("  ecall\n");
        out.append("  li a1, 10\n");
        out.append("  li a0, @print_char\n");
        out.append("  ecall\n");
        out.append("  li a0, @exit\n");
        out.append("  ecall\n");
        out.append("abort_17:\n");
        out.append("  j abort_17\n");
        out.append(".globl alloc\n");
        out.append("alloc:\n");
        out.append("  mv a1, a0\n");
        out.append("  li a0, @sbrk\n");
        out.append("  ecall\n");
        out.append("  jr ra\n");
        out.append(".data\n");
        out.append(".globl msg_nullptr\n");
        out.append("msg_nullptr:\n");
        out.append("  .asciiz \"null pointer\"\n");
        out.append("  .align 2\n");
        out.append(".globl msg_array_oob\n");
        out.append("msg_array_oob:\n");
        out.append("  .asciiz \"array index out of bounds\"\n");
        out.append("  .align 2\n");
        out.append(".text\n");

        for (FunctionDecl fn : program.funDecls) {
            boolean isDirectEntry = entryName.equals("main")
                && fn.functionName.toString().equals("main");
            compileFunction(fn, out, isDirectEntry);
        }
        System.out.print(out);
    }

    static void compileFunction(FunctionDecl fn, StringBuilder out, boolean isDirectEntry) {
        //collect the IDs that need stack slots
        //assign the fp-relatice offsets
            //fp-4 = saved ra; fp-8= saved fp


        String fname = fn.functionName.toString();
        List<Identifier> params = fn.formalParameters;
        List<Instruction> instrs = fn.block.instructions;
        Identifier retId = fn.block.return_id;


        Set<String> idSet = new LinkedHashSet<>();
        for (Identifier p : params) {
            idSet.add(p.toString());
        }
        for (Instruction ins : instrs) {
            collectIds(ins, idSet);
        }
        if (retId != null) {
            idSet.add(retId.toString());
        }


        Map<String, Integer> offsets = new LinkedHashMap<>();
        int off = -12;
        for (String id : idSet) {
            offsets.put(id, off);
            off -= 4;
        }

        int frameSize = 8 + idSet.size() * 4;
        //align to mult of 4(?) ; might not need
        if (frameSize % 16 != 0) {
            frameSize = ((frameSize / 16) + 1) * 16;
        }

        out.append(".globl ").append(fname).append("\n");
        out.append(fname).append(":\n");


        //prologue; save caller fp, then fp = top of caller's frame
        out.append("  sw fp, -8(sp)\n");
        out.append("  mv fp, sp\n");
        out.append("  li t0, ").append(frameSize).append("\n");
        out.append("  sub sp, sp, t0\n");
        out.append("  sw ra, -4(fp)\n");

        //store incoming args into param slots
        String[] argRegs = {"a0","a1","a2","a3","a4","a5","a6","a7"};
        for (int i = 0; i < params.size() && i < 8; i++) {
            int poff = offsets.get(params.get(i).toString());
            out.append("  sw ").append(argRegs[i]).append(", ").append(poff).append("(fp)\n");
        }
        for (int i = 8; i < params.size(); i++) {
            int poff = offsets.get(params.get(i).toString());
            out.append("  lw t0, ").append((i - 7) * 4).append("(fp)\n");
            out.append("  sw t0, ").append(poff).append("(fp)\n");
        }
        
        //emit intsr
        for (Instruction ins : instrs) {
            emitInstruction(ins, offsets, fname, out);
        }

        //epilogue
        if (retId != null) {
            int roff = offsets.get(retId.toString());
            out.append("  lw a0, ").append(roff).append("(fp)\n");
        } 
        else {
            out.append("  li a0, 0\n");
        }


        out.append("  lw ra, -4(fp)\n");
        out.append("  lw fp, -8(fp)\n");
        out.append("  li t0, ").append(frameSize).append("\n");
        out.append("  add sp, sp, t0\n");

        
        if (isDirectEntry) {
            //venus calls directly with ra=0
                //**use @exit instead of jr ra
            out.append("  li a0, @exit\n");
            out.append("  ecall\n\n");
        } 
        else {
            out.append("  jr ra\n\n");
        }
    }

    static int branchCounter = 0;

    static boolean isPhysReg(String name) {
        return Registers.riscVregs.contains(name);
    }

    static void addIfId(String name, Set<String> ids) {
        if (!isPhysReg(name)) {
            ids.add(name);
        }
    }

    static void collectIds(Instruction ins, Set<String> ids) {
        if (ins instanceof Move_Id_Reg) {
            ids.add(((Move_Id_Reg)ins).lhs.toString());
        } 
        else if (ins instanceof Move_Reg_Id) {
            ids.add(((Move_Reg_Id)ins).rhs.toString());
        } 
        else if (ins instanceof Call) {
            Call c = (Call)ins;
            ids.add(c.lhs.toString());
            addIfId(c.callee.toString(), ids);
            for (Identifier a : c.args) {
                addIfId(a.toString(), ids);
            }
        } 
        else if (ins instanceof Alloc) {
            addIfId(((Alloc)ins).lhs.toString(), ids);
            addIfId(((Alloc)ins).size.toString(), ids);

        } 
        else if (ins instanceof Load) {
            addIfId(((Load)ins).lhs.toString(), ids);
            addIfId(((Load)ins).base.toString(), ids);
        } 
        else if (ins instanceof Store) {
            addIfId(((Store)ins).base.toString(), ids);
            addIfId(((Store)ins).rhs.toString(), ids);

        } 
        else if (ins instanceof Move_Reg_Integer) {
            addIfId(((Move_Reg_Integer)ins).lhs.toString(), ids);

        } 
        else if (ins instanceof Move_Reg_FuncName) {
            addIfId(((Move_Reg_FuncName)ins).lhs.toString(), ids);

        } 
        else if (ins instanceof Print) {
            addIfId(((Print)ins).content.toString(), ids);
        } 

        else if (ins instanceof IfGoto) {
            addIfId(((IfGoto)ins).condition.toString(), ids);
        }
    }

    static void loadId(String id, String reg, Map<String, Integer> offsets, StringBuilder out) {
        Integer o = offsets.get(id);
        if (o != null) {
            out.append("  lw ").append(reg).append(", ").append(o).append("(fp)\n");
        } else {
            out.append("  li ").append(reg).append(", 0  # unknown: ").append(id).append("\n");
        }
    }

    static void storeId(String id, String reg, Map<String, Integer> offsets, StringBuilder out) {
        Integer o = offsets.get(id);
        if (o != null) {
            out.append("  sw ").append(reg).append(", ").append(o).append("(fp)\n");
        }
    }

    //unique label per fn
    static String label(String lbl, String fname) {
        return fname + "_" + lbl;
    }

    static void emitInstruction(Instruction ins, Map<String, Integer> offsets,
                                 String fname, StringBuilder out) {
        if (ins instanceof LabelInstr) {
            out.append(label(((LabelInstr)ins).label.toString(), fname)).append(":\n");

        } 
        else if (ins instanceof Move_Reg_Integer) {
            Move_Reg_Integer m = (Move_Reg_Integer)ins;
            String lhsName = m.lhs.toString();
            if (isPhysReg(lhsName)) {
                out.append("  li ").append(lhsName).append(", ").append(m.rhs).append("\n");
            } 
            else {
                out.append("  li t0, ").append(m.rhs).append("\n");
                storeId(lhsName, "t0", offsets, out);
            }

        } 
        else if (ins instanceof Move_Reg_FuncName) {
            Move_Reg_FuncName m = (Move_Reg_FuncName)ins;
            String lhsName = m.lhs.toString();
            if (isPhysReg(lhsName)) {
                out.append("  la ").append(lhsName).append(", ").append(m.rhs).append("\n");
            } 
            else {
                out.append("  la t0, ").append(m.rhs).append("\n");
                storeId(lhsName, "t0", offsets, out);
            }

        } 
        else if (ins instanceof Move_Reg_Reg) {
            Move_Reg_Reg m = (Move_Reg_Reg)ins;
            if (!m.lhs.toString().equals(m.rhs.toString())) {
                out.append("  mv ").append(m.lhs).append(", ").append(m.rhs).append("\n");
            }

        } 
        else if (ins instanceof Move_Id_Reg) {
            Move_Id_Reg m = (Move_Id_Reg)ins;
            String rhsName = m.rhs.toString();
            if (isPhysReg(rhsName)) {
                storeId(m.lhs.toString(), rhsName, offsets, out);
            } 
            else {
                loadId(rhsName, "t0", offsets, out);
                storeId(m.lhs.toString(), "t0", offsets, out);
            }

        } 
        else if (ins instanceof Move_Reg_Id) {
            Move_Reg_Id m = (Move_Reg_Id)ins;
            loadId(m.rhs.toString(), m.lhs.toString(), offsets, out);

        } 
        else if (ins instanceof Add) {
            Add a = (Add)ins;
            out.append("  add ").append(a.lhs).append(", ").append(a.arg1).append(", ").append(a.arg2).append("\n");

        } 
        else if (ins instanceof Subtract) {
            Subtract s = (Subtract)ins;
            out.append("  sub ").append(s.lhs).append(", ").append(s.arg1).append(", ").append(s.arg2).append("\n");

        } 
        else if (ins instanceof Multiply) {
            Multiply m = (Multiply)ins;
            out.append("  mul ").append(m.lhs).append(", ").append(m.arg1).append(", ").append(m.arg2).append("\n");

        } 
        else if (ins instanceof LessThan) {
            LessThan lt = (LessThan)ins;
            out.append("  slt ").append(lt.lhs).append(", ").append(lt.arg1).append(", ").append(lt.arg2).append("\n");

        } 
        else if (ins instanceof Load) {
            Load l = (Load)ins;
            String lhsName = l.lhs.toString();
            String baseName = l.base.toString();
            //resolve base
                //if identifier: load into t1
            String base;
            if (isPhysReg(baseName)) {
                base = baseName;
            } 
            else {
                loadId(baseName, "t1", offsets, out);
                base = "t1";
            }
            //emit load
                //if lhs is physical reg ==> load directly
                //else ==> load to t0, store to slot
            if (isPhysReg(lhsName)) {
                out.append("  lw ").append(lhsName).append(", ").append(l.offset)
                   .append("(").append(base).append(")\n");
            } 
            else {
                out.append("  lw t0, ").append(l.offset).append("(").append(base).append(")\n");
                storeId(lhsName, "t0", offsets, out);
            }

        } else if (ins instanceof Store) {
            Store s = (Store)ins;
            String baseName = s.base.toString();
            String rhsName = s.rhs.toString();
            //resolve rhs first 
                //use t0 unless base=t0 physical ==> then use t1
            String rhsReg;
            if (isPhysReg(rhsName)) {
                rhsReg = rhsName;
            } 
            else {
                String rhsTemp = (isPhysReg(baseName) && baseName.equals("t0")) ? "t1" : "t0";
                loadId(rhsName, rhsTemp, offsets, out);
                rhsReg = rhsTemp;
            }
            //resolve base - use t1, unless rhsReg=t1 then t0
            String baseReg;
            if (isPhysReg(baseName)) {
                baseReg = baseName;
            } 
            else {
                String baseTemp = rhsReg.equals("t1") ? "t0" : "t1";
                loadId(baseName, baseTemp, offsets, out);
                baseReg = baseTemp;
            }
            out.append("  sw ").append(rhsReg).append(", ").append(s.offset).append("(").append(baseReg).append(")\n");

        } 
        else if (ins instanceof Alloc) {
            Alloc a = (Alloc)ins;
            String sizeName = a.size.toString();
            if (isPhysReg(sizeName)) {
                out.append("  mv a0, ").append(sizeName).append("\n");
            } 
            else {
                loadId(sizeName, "a0", offsets, out);
            }
            out.append("  jal alloc\n");
            String lhsName = a.lhs.toString();
            if (isPhysReg(lhsName)) {
                out.append("  mv ").append(lhsName).append(", a0\n");
            } 
            else {
                storeId(lhsName, "a0", offsets, out);
            }

        } else if (ins instanceof Print) {
            Print p = (Print)ins;
            String contentName = p.content.toString();
            if (isPhysReg(contentName)) {
                out.append("  mv a0, ").append(contentName).append("\n");
            } else {
                loadId(contentName, "a0", offsets, out);
            }

            out.append("  jal print\n");

        } 
        else if (ins instanceof ErrorMessage) {
            ErrorMessage e = (ErrorMessage)ins;
            String msgLabel = e.msg.contains("array") ? "msg_array_oob" : "msg_nullptr";
            out.append("  la a0, ").append(msgLabel).append("\n");
            out.append("  jal error\n");

        } 
        else if (ins instanceof sparrowv.Goto) {
            out.append("  j ").append(label(((sparrowv.Goto)ins).label.toString(), fname)).append("\n");

        } 
        else if (ins instanceof IfGoto) {
            IfGoto ig = (IfGoto)ins;
            String condName = ig.condition.toString();
            String condReg;
            if (isPhysReg(condName)) {
                condReg = condName;
            } 
            else {
                loadId(condName, "t0", offsets, out);
                condReg = "t0";
            }
            //if cond != 0
                //branch to skip (in range)
            //if cond == 0
                //fall to j farLabel
            String skipLabel = fname + "_br" + (branchCounter++);
            out.append("  bnez ").append(condReg).append(", ").append(skipLabel).append("\n");
            out.append("  j ").append(label(ig.label.toString(), fname)).append("\n");
            out.append(skipLabel).append(":\n");

        } 
        else if (ins instanceof Call) {
            emitCall((Call)ins, offsets, out);
        }
    }

    static void emitCall(Call c, Map<String, Integer> offsets, StringBuilder out) {
        List<Identifier> args = c.args;
        String[] argRegs = {"a0","a1","a2","a3","a4","a5","a6","a7"};
        int stackArgs = Math.max(0, args.size() - 8);

        //push stack args beyond 8 to stack
        if (stackArgs > 0) {
            out.append("  addi sp, sp, -").append(stackArgs * 4).append("\n");
            for (int i = 8; i < args.size(); i++) {
                String argName = args.get(i).toString();
                if (isPhysReg(argName)) {
                    out.append("  sw ").append(argName).append(", ").append((i - 8) * 4).append("(sp)\n");
                } 
                else {
                    loadId(argName, "t0", offsets, out);
                    out.append("  sw t0, ").append((i - 8) * 4).append("(sp)\n");
                }
            }
        }

        //load 1st 8 args into arg regs
        for (int i = 0; i < args.size() && i < 8; i++) {
            String argName = args.get(i).toString();
            if (isPhysReg(argName)) {
                if (!argName.equals(argRegs[i]))
                    out.append("  mv ").append(argRegs[i]).append(", ").append(argName).append("\n");
            } 
            else {
                loadId(argName, argRegs[i], offsets, out);
            }
        }

        //resolve callee after arg loading 
            //then t0 != needed for stack args
        String calleeName = c.callee.toString();
        String calleeReg;
        if (isPhysReg(calleeName)) {
            calleeReg = calleeName;
        } 
        else {
            loadId(calleeName, "t0", offsets, out);
            calleeReg = "t0";
        }

        //call via callee reg
        out.append("  jalr ").append(calleeReg).append("\n");

        //clean up stack args
        if (stackArgs > 0) {
            out.append("  addi sp, sp, ").append(stackArgs * 4).append("\n");
        }

        //propagate ret val
            //if lhs == physical reg, mv
            //always spill to stack slot
        if (isPhysReg(c.lhs.toString())) {
            out.append("  mv ").append(c.lhs).append(", a0\n");
        }
        storeId(c.lhs.toString(), "a0", offsets, out);
    }
}