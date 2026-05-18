import minijava.syntaxtree.*;
import minijava.visitor.*;
import minijava.MiniJavaParser;
import java.util.*;

public class J2S {
    //cpy from Typecheck.java
    static String mainCN;
    static Map<String, String> clparent = new LinkedHashMap<>();
    static Map<String, Map<String, String>> cflds = new HashMap<>();
    static Map<String, Map<String, MethodInfo>> cmtds = new HashMap<>();
    static Map<String, List<String>> cvtable = new LinkedHashMap<>();
    static Map<String, Map<String, Integer>> coffsets = new LinkedHashMap<>();
    static String lastType = null;

    static final Set<String> RESERVED = new HashSet<>(Arrays.asList(
        "a2","a3","a4","a5","a6","a7",
        "s1","s2","s3","s4","s5","s6","s7","s8","s9","s10","s11",
        "t0","t1","t2","t3","t4","t5"
    ));

    static String safeName(String name) {
        return RESERVED.contains(name) ? "p_" + name : name;
    }

    static boolean isSub(String t1, String t2) {
        if (t1==null || t2==null) {
            return false;
        }
        if (t1.equals(t2)) {
            return true;
        }
        String parent = clparent.get(t1); //null == primitives or root class
        if (parent==null) {
            return false;
        }
        return isSub(parent,t2);
    }


    static class fpVisitor extends GJDepthFirst<String, Void> {

        @Override
        public String visit(Goal n, Void a) {
            String mainName = n.f0.f1.f0.tokenImage;
            mainCN = mainName;
            clparent.put(mainName, null);
            cflds.put(mainName, new LinkedHashMap<>());
            cmtds.put(mainName, new LinkedHashMap<>());
            n.f1.accept(this, a);
            return null;
        }

        @Override
        public String visit(ClassDeclaration n, Void a) {
            String name = n.f1.f0.tokenImage;
            if (clparent.containsKey(name)) {
                throw new RuntimeException("type error");
            }
            clparent.put(name, null);
            Map<String, String> fields = new LinkedHashMap<>();
            for (Enumeration<Node> e = n.f3.elements(); e.hasMoreElements();) {
                VarDeclaration vd = (VarDeclaration) e.nextElement();
                String fname = vd.f1.f0.tokenImage;
                if (fields.containsKey(fname)) {
                    throw new RuntimeException("type error");
                }
                fields.put(fname, J2S.toString(vd.f0));
            }
            Map<String, MethodInfo> methods = new LinkedHashMap<>();
            for (Enumeration<Node> e = n.f4.elements(); e.hasMoreElements();) {
                MethodDeclaration md = (MethodDeclaration) e.nextElement();
                String mname = md.f2.f0.tokenImage;
                if (methods.containsKey(mname)) {
                    throw new RuntimeException("type error");
                }
                methods.put(mname, buildMTD(md));
            }
            cflds.put(name, fields);
            cmtds.put(name, methods);
            return null;
        }

        @Override
        public String visit(ClassExtendsDeclaration n, Void a) {
            String name = n.f1.f0.tokenImage;
            String parent = n.f3.f0.tokenImage;
            if (clparent.containsKey(name)) {
                throw new RuntimeException("type error");
            }
            clparent.put(name, parent);
            Map<String, String> fields = new LinkedHashMap<>();
            for (Enumeration<Node> e = n.f5.elements(); e.hasMoreElements();) {
                VarDeclaration vd = (VarDeclaration) e.nextElement();
                String fname = vd.f1.f0.tokenImage;
                if (fields.containsKey(fname)) {
                    throw new RuntimeException("type error");
                }
                fields.put(fname, J2S.toString(vd.f0));
            }
            Map<String, MethodInfo> methods = new LinkedHashMap<>();
            for (Enumeration<Node> e = n.f6.elements(); e.hasMoreElements();) {
                MethodDeclaration md = (MethodDeclaration) e.nextElement();
                String mname = md.f2.f0.tokenImage;
                if (methods.containsKey(mname)) {
                    throw new RuntimeException("type error");
                }
                methods.put(mname, buildMTD(md));
            }
            cflds.put(name, fields);
            cmtds.put(name, methods);
            return null;
        }
    }

    static String toString(Type t) {
        //look at AST type node,
            //if its array return int, bool bool, int int , 
            //elwe its smthing else so return the ID name
        Node n = t.f0.choice;
        if (n instanceof ArrayType) {
            return "int[]";
        }
        if (n instanceof BooleanType){
            return "boolean";
        }
        if (n instanceof IntegerType) {
            return "int";
        }
        return ((Identifier) n).f0.tokenImage; 
    }

    static class MethodInfo {
        List<String> paramNames = new ArrayList<>();
        List<String> paramTypes = new ArrayList<>();
        String returnType;
    }


    static MethodInfo buildMTD(MethodDeclaration md) {
        MethodInfo info = new MethodInfo();
        info.returnType = toString(md.f1);

        if (md.f4.present()) {
            FormalParameterList fpl = (FormalParameterList) md.f4.node;
            //first param
            info.paramNames.add(fpl.f0.f1.f0.tokenImage);
            info.paramTypes.add(toString(fpl.f0.f0));
            //remaining params
            for (Enumeration<Node> e = fpl.f1.elements(); e.hasMoreElements(); ) {
                FormalParameterRest fpr = (FormalParameterRest) e.nextElement();
                info.paramNames.add(fpr.f1.f1.f0.tokenImage);
                info.paramTypes.add(toString(fpr.f1.f0));
            }
        }
        return info;
    }


    static void validHierarch() {
        for (Map.Entry<String, String> e : clparent.entrySet()) { //parent named in "extends" must == declared class
            String parent = e.getValue();
            if (parent != null && !clparent.containsKey(parent)) {
                throw new RuntimeException("type error");
            }
        }

        for (String cls : clparent.keySet()) { //inheritance == acrylic (walk each class' parent chain)
            Set<String> visited = new HashSet<>();
            String cur = cls;
            while (cur != null) {
                if (!visited.add(cur)) { //if see class twice == cycle
                    throw new RuntimeException("type error");
                }
                cur = clparent.get(cur);
            }
        }

        for (String cls : clparent.keySet()) { //all class-typed names used in fld/mtd decl have to exist
            for (String t : cflds.get(cls).values()) {
                primOrCLName(t);
            }
            for (MethodInfo m : cmtds.get(cls).values()) {
                primOrCLName(m.returnType);
                for (String pt : m.paramTypes) {
                    primOrCLName(pt);
                }
            }
        }

        for (Map.Entry<String, String> e : clparent.entrySet()) { //no overloading; in parent, sig must == exactly (params&return)
            String cls= e.getKey();
            String parent = e.getValue();
            if (parent == null) {
                continue;
            }
            for (Map.Entry<String, MethodInfo> me : cmtds.get(cls).entrySet()) {
                MethodInfo pSig = findMTD(parent, me.getKey());
                if (pSig != null && !doSigsMatch(me.getValue(), pSig)) {
                    throw new RuntimeException("type error");
                }
            }
        }
    }

    static void emitSkeleton(StringBuilder sb) {
        //vtable: load vtable ptr from [obj+0], then olad fn ptr from [vtable + slot*4], then call it
        //sparrow == no global variables or static data sections --> ok to allov vtable on heap per obj
        //main first (sparrow rule: 1st fn == 0 param)
        // sb.append("func ").append(mainCN).append("()\n");
        // sb.append("  ret = 0\n");
        // sb.append("  return ret\n\n");

        //vtinit each non-main cl
        for (String cls : cvtable.keySet()) {
            List<String> vt = cvtable.get(cls);
            sb.append("func ").append(cls).append("_vtinit(this)\n");
            sb.append("  vtsize = ").append(vt.size() * 4).append("\n");
            sb.append("  vt = alloc(vtsize)\n");
            for (int i = 0; i < vt.size(); i++) {
                sb.append("  vfp").append(i).append(" = @").append(vt.get(i)).append("\n");
                sb.append("  [vt+").append(i * 4).append("] = vfp").append(i).append("\n");
            }
            sb.append("  [this+0] = vt\n");
            sb.append("  ret = 0\n");
            sb.append("  return ret\n\n");
        }


        // for (String cls : clparent.keySet()) {
        //     if (cls.equals(mainCN)) {
        //         continue;
        //     }
        //     for (String mname : cmtds.get(cls).keySet()) {
        //         MethodInfo info = cmtds.get(cls).get(mname);
        //         sb.append("func ").append(cls).append("_").append(mname).append("(this");
        //         for (String p : info.paramNames) {
        //             sb.append(" ").append(p);
        //         }

        //         sb.append(")\n");
        //         sb.append("  ret = 0\n");
        //         sb.append("  return ret\n\n");
        //     }
        // }
    }


    static boolean doSigsMatch(MethodInfo a, MethodInfo b) { 
        if (!a.returnType.equals(b.returnType)) {
            return false;
        }
        if (a.paramTypes.size() != b.paramTypes.size()) {
            return false;
        }
        for (int i = 0; i < a.paramTypes.size(); i++) {
            if (!a.paramTypes.get(i).equals(b.paramTypes.get(i))) {
                return false;
            }
        }
        return true;
    }

    //reject if t == undecl class name
    static void primOrCLName(String t) {
        if (t.equals("int") || t.equals("boolean") || t.equals("int[]")) {
            return;
        }
        if (!clparent.containsKey(t)) {
            throw new RuntimeException("type error");
        }
    }

    static MethodInfo findMTD(String cls, String mname) {
        if (cls == null || !clparent.containsKey(cls)) {
            return null;
        }
        MethodInfo m = cmtds.get(cls).get(mname);
        if (m != null) {
            return m;
        }
        return findMTD(clparent.get(cls), mname);
    }


    //add a formal parameter == enforce uniqueness
    static void addParam(FormalParameter fp, Map<String, String> env, Set<String> seen) {
        String name = fp.f1.f0.tokenImage;
        if (!seen.add(name)) {
            throw new RuntimeException("type error");
        }
        String t = toString(fp.f0);
        primOrCLName(t);
        env.put(name, t);
    }

    static void computeLayout() {
        for (String cls:clparent.keySet()){
            if (cls.equals(mainCN)) {
                continue;
            }

            List<String> vtable = new ArrayList<>();
            String parent = clparent.get(cls);
            if (parent != null && cvtable.containsKey(parent)) {
                vtable.addAll(cvtable.get(parent));
            }
            for (String mname : cmtds.get(cls).keySet()) {
                String entry = cls + "_" + mname;
                int slot = -1;
                for (int i = 0; i < vtable.size(); i++) {
                    String existing = vtable.get(i);
                    String existingMtd = existing.substring(existing.indexOf('_') + 1);
                    if (existingMtd.equals(mname)) { 
                        slot = i; 
                        break; 
                    }
                }
                if (slot >= 0) {
                    vtable.set(slot, entry);
                } 
                else {
                    vtable.add(entry);
                }
            }
            cvtable.put(cls, vtable);

            Map<String, Integer> offsets = new LinkedHashMap<>();
            int offset = 4;
            List<String> chain = new ArrayList<>();
            String cur2 = cls;
            while (cur2 != null && !cur2.equals(mainCN)) {
                chain.add(0, cur2);
                cur2 = clparent.get(cur2);
            }
            for (String c : chain) {
                for (String fname : cflds.get(c).keySet()) {
                    offsets.put(c + "_" + fname, offset);
                    offset += 4;
                }
            }
            coffsets.put(cls,offsets);
        }
    }

    //parent fields first, then new fields override
    static Map<String, String> makeFLDMap(String cls) {
        Map<String, String> result = new LinkedHashMap<>();
        if (cls == null) {
            return result;
        }
        String parent = clparent.get(cls);
        if (parent != null) {
            result.putAll(makeFLDMap(parent));
        }
        result.putAll(cflds.get(cls));
        return result;
    }



    static class CgCtx {
        String cls;
        int tempCount = 0;
        int labelCount = 0;
        StringBuilder sb;
        Set<String> locals = new HashSet<>();
        Map<String, String> localTypes = new HashMap<>();


        CgCtx(String cls, StringBuilder sb) {
            this.cls = cls;
            this.sb  = sb;
        }

        String newTemp()  { 
            return "tmp" + (tempCount++); 
        }
        String newLabel() { 
            return "lbl" + (labelCount++); 
        }

        void emit(String line) { 
            sb.append("  ").append(line).append("\n"); 
        }
        void emitLabel(String label) { 
            sb.append("  ").append(label).append(":\n"); 
        }
    }

    static class cgVisitor extends GJDepthFirst<String, CgCtx> {
        @Override
        public String visit(Goal n, CgCtx ctx) {
            n.f0.accept(this, ctx); //f0 --> main; f1 --> all the other classes
            n.f1.accept(this, ctx);
            return null;
        }

        @Override
        public String visit(MainClass n, CgCtx ctx) {
            ctx.sb.append("func ").append(mainCN).append("()\n");
            ctx.locals.clear();
            ctx.localTypes.clear();

            for (Enumeration<Node> e = n.f14.elements(); e.hasMoreElements();) {
                VarDeclaration vd = (VarDeclaration) e.nextElement();
                String vname = vd.f1.f0.tokenImage;
                String vtype = J2S.toString(vd.f0); 
                ctx.locals.add(vname);
                ctx.localTypes.put(vname,vtype);
                // ctx.locals.add(vd.f1.f0.tokenImage);

            }
            for (Enumeration<Node> e = n.f15.elements(); e.hasMoreElements();) {
                ((Statement) e.nextElement()).accept(this, ctx);
            }
            String ret = ctx.newTemp();
            ctx.emit(ret + " = 0");
            ctx.sb.append("  return ").append(ret).append("\n\n");

            return null;
        }

        @Override
        public String visit(Statement n,CgCtx ctx) {
            return n.f0.accept(this, ctx);
        }

        @Override
        public String visit(PrintStatement n,CgCtx ctx) {
            String val = n.f2.accept(this, ctx);
            ctx.emit("print(" + val + ")");
            return null;
        }

        @Override
        public String visit(Expression n,CgCtx ctx) {
            return n.f0.accept(this, ctx);
        }

        @Override
        public String visit(PrimaryExpression n, CgCtx ctx) {
            return n.f0.accept(this, ctx);
        }

        @Override
        public String visit(IntegerLiteral n, CgCtx ctx) {
            String t = ctx.newTemp();
            ctx.emit(t + " = " + n.f0.tokenImage);
            return t;
        }

        @Override
        public String visit(PlusExpression n, CgCtx ctx) {
            String l = n.f0.accept(this, ctx);
            String r = n.f2.accept(this, ctx);
            String t = ctx.newTemp();
            ctx.emit(t + " = " + l + " + " + r);
            return t;
        }

        @Override
        public String visit(ClassDeclaration n, CgCtx ctx) {
            String savedCls = ctx.cls;
            ctx.cls = n.f1.f0.tokenImage;
            for (Enumeration<Node> e =n.f4.elements();e.hasMoreElements();) {
                ((MethodDeclaration) e.nextElement()).accept(this, ctx);
            }
            ctx.cls = savedCls;
            return null;
        }

        @Override
        public String visit(ClassExtendsDeclaration n, CgCtx ctx) {
            String savedCls = ctx.cls;
            ctx.cls = n.f1.f0.tokenImage;
            for (Enumeration<Node> e =n.f6.elements();e.hasMoreElements();) {
                ((MethodDeclaration) e.nextElement()).accept(this, ctx);
            }
            ctx.cls = savedCls;
            return null;
        }

        @Override
        public String visit(MethodDeclaration n, CgCtx ctx) {
            String mname = n.f2.f0.tokenImage;
            MethodInfo info = cmtds.get(ctx.cls).get(mname);

            //emit fn sig
            ctx.sb.append("func ").append(ctx.cls).append("_").append(mname).append("(this");
            ctx.locals.clear();
            ctx.localTypes.clear();  
            ctx.locals.add("this");
            ctx.localTypes.put("this", ctx.cls);
            for (String p : info.paramNames) {
                String sp = safeName(p);
                ctx.sb.append(" ").append(sp);
                ctx.locals.add(sp);
                ctx.localTypes.put(sp, info.paramTypes.get(info.paramNames.indexOf(p)));
                if (!sp.equals(p)) {
                    ctx.localTypes.put(p, info.paramTypes.get(info.paramNames.indexOf(p)));
                }
            }
            ctx.sb.append(")\n");

            for (Enumeration<Node> e = n.f7.elements(); e.hasMoreElements();) { //loc var decl
                VarDeclaration vd = (VarDeclaration) e.nextElement();
                String vname = vd.f1.f0.tokenImage;
                String vtype =J2S.toString(vd.f0);
                ctx.locals.add(vname);
                ctx.localTypes.put(vname,vtype);
                ctx.emit(vname+ " = 0");
            }

            for (Enumeration<Node> e = n.f8.elements(); e.hasMoreElements();) { //stmts
                ((Statement) e.nextElement()).accept(this, ctx);
            }

            //ret expr
            String retVal = n.f10.accept(this, ctx);
            ctx.sb.append("  return ").append(retVal).append("\n\n");


            return null;
        }

        @Override
        public String visit(TrueLiteral n,CgCtx ctx) {
            String t = ctx.newTemp();
            ctx.emit(t + " = 1");
            return t;
        }

        @Override
        public String visit(FalseLiteral n,CgCtx ctx) {
            String t = ctx.newTemp();
            ctx.emit(t + " = 0");
            return t;
        }

        @Override
        public String visit(Identifier n, CgCtx ctx) {
            String name = n.f0.tokenImage;
            String safeName = safeName(name);
            if (ctx.locals.contains(safeName)) { //then ==local var/param
                lastType = ctx.localTypes.get(safeName);
                return safeName;
            }

            String dc = ctx.cls;
            while (dc != null && !(cflds.containsKey(dc) && cflds.get(dc).containsKey(name))) {
                dc = clparent.get(dc);
            }
            int offset = coffsets.get(ctx.cls).get(dc + "_" + name);
            String t = ctx.newTemp();
            ctx.emit(t + " = [this+" + offset + "]");
            lastType = cflds.get(dc).get(name);

            return t;
        }

        @Override
        public String visit(ThisExpression n,CgCtx ctx) {
            lastType = ctx.cls;
            return "this";
        }

        @Override
        public String visit(BracketExpression n, CgCtx ctx) {
            return n.f1.accept(this, ctx);
        }

        @Override
        public String visit(AllocationExpression n, CgCtx ctx) {
            String cls = n.f1.f0.tokenImage;
            // int numFields = makeFLDMap(cls).size();
            int numFields = coffsets.get(cls).size();
            int bytes = (numFields + 1) * 4; // +1 for vtable ptr

            String tsize = ctx.newTemp();
            String obj   = ctx.newTemp();
            String tvt   = ctx.newTemp();

            ctx.emit(tsize + " = " + bytes);
            ctx.emit(obj   + " = alloc(" + tsize + ")");
            ctx.emit(tvt   + " = @" + cls + "_vtinit");
            //must discard into temp
            // ctx.emit("call " + tvt + "(" + obj + ")");
            String tdiscard = ctx.newTemp();
            ctx.emit(tdiscard + " = call " + tvt + "(" + obj + ")");

            lastType = cls;
            return obj;
        }

        @Override
        public String visit(MessageSend n,CgCtx ctx) {
            //first codegen the receiver object, 
            //then get static type of the receiver (so we know which vtable to look up)
            //codegen the arguments --> find the method's vtable slot
            //load vtable ptr, then fn ptr
            //call: this + args

            String obj = n.f0.accept(this, ctx);
            String recvType = lastType;

            String lblNotNull = ctx.newLabel();
            String lblNull = ctx.newLabel();
            ctx.emit("if0 " + obj + " goto " + lblNull);
            ctx.emit("goto " + lblNotNull);
            ctx.emitLabel(lblNull);
            ctx.emit("error(\"null pointer\")");
            ctx.emitLabel(lblNotNull);

            List<String> argTemps = new ArrayList<>();
            if (n.f4.present()) {
                ExpressionList el = (ExpressionList) n.f4.node;
                argTemps.add(el.f0.accept(this, ctx));
                for (Enumeration<Node> e = el.f1.elements(); e.hasMoreElements();) {
                    argTemps.add(((ExpressionRest) e.nextElement()).f1.accept(this, ctx));
                }
            }

            String mname = n.f2.f0.tokenImage;
            int slot = -1;
            //try recvType's vtable directly
            List<String> vt = cvtable.get(recvType);
            if (vt != null) {
                for (int i = 0; i < vt.size(); i++) {
                    String entryMethod = vt.get(i).substring(vt.get(i).indexOf('_') + 1);
                    if (entryMethod.equals(mname)) { slot = i; break; }
                }
            }
            //if not found
                //find which class defines it and search all vtables for the slot
            if (slot == -1) {
                for (List<String> anyVt : cvtable.values()) {
                    for (int i = 0; i < anyVt.size(); i++) {
                        String entryMethod = anyVt.get(i).substring(anyVt.get(i).indexOf('_') + 1);
                        if (entryMethod.equals(mname)) { slot = i; break; }
                    }
                    if (slot != -1) break;
                }
            }

            String tvt = ctx.newTemp();
            String tfp = ctx.newTemp();
            String result = ctx.newTemp();

            ctx.emit(tvt + " = [" + obj + "+0]");
            ctx.emit(tfp + " = [" + tvt + "+" + (slot * 4) + "]");

            StringBuilder call = new StringBuilder();
            call.append(result + " = call " + tfp + "(" + obj);
            for (String arg : argTemps) {
                call.append(" ").append(arg);
            }
            call.append(")");
            ctx.emit(call.toString());

            MethodInfo mtdInfo = findMTD(recvType,mname);
            if (mtdInfo != null) {
                lastType = mtdInfo.returnType;
            }

            return result;
        }

        @Override
        public String visit(AssignmentStatement n, CgCtx ctx) {
            String varName = n.f0.f0.tokenImage;
            String rhs = n.f2.accept(this, ctx);
            
            if (ctx.locals.contains(varName)) {
                ctx.emit(varName + " = " + rhs);
            } 
            else { //fld assingment
                String dc = ctx.cls;
                while (dc != null && !(cflds.containsKey(dc) && cflds.get(dc).containsKey(varName))) {
                    dc = clparent.get(dc);
                }
                int offset = coffsets.get(ctx.cls).get(dc + "_" + varName);
                ctx.emit("[this+" + offset + "] = " + rhs);
            }

            return null;
        }

        @Override
        public String visit(Block n,CgCtx ctx) {
            for (Enumeration<Node> e = n.f1.elements(); e.hasMoreElements();) {
                ((Statement) e.nextElement()).accept(this, ctx);
            }
            return null;
        }

        @Override
        public String visit(IfStatement n, CgCtx ctx) {
            String lblElse = ctx.newLabel();
            String lblEnd  = ctx.newLabel();
            String cond = n.f2.accept(this, ctx);

            ctx.emit("if0 " + cond + " goto " + lblElse);
            n.f4.accept(this, ctx);
            ctx.emit("goto " + lblEnd);
            ctx.emitLabel(lblElse);
            n.f6.accept(this, ctx);
            ctx.emitLabel(lblEnd);

            return null;
        }

        @Override
        public String visit(WhileStatement n, CgCtx ctx) {
            String lblTop = ctx.newLabel();
            String lblEnd = ctx.newLabel();

            ctx.emitLabel(lblTop);
            String cond = n.f2.accept(this, ctx);
            ctx.emit("if0 " + cond + " goto " + lblEnd);
            n.f4.accept(this, ctx);
            ctx.emit("goto " + lblTop);
            ctx.emitLabel(lblEnd);

            return null;
        }

        @Override
        public String visit(AndExpression n, CgCtx ctx) {
            String lblFalse = ctx.newLabel();
            String lblEnd = ctx.newLabel();
            String result = ctx.newTemp();

            String left = n.f0.accept(this, ctx);
            ctx.emit("if0 " + left + " goto " + lblFalse);
            String right = n.f2.accept(this, ctx);
            ctx.emit("if0 " + right + " goto " + lblFalse);
            ctx.emit(result + " = 1");
            ctx.emit("goto " + lblEnd);
            ctx.emitLabel(lblFalse);
            ctx.emit(result + " = 0");
            ctx.emitLabel(lblEnd);

            return result;
        }

        @Override
        public String visit(MinusExpression n, CgCtx ctx) {
            String l = n.f0.accept(this, ctx);
            String r = n.f2.accept(this, ctx);
            String t = ctx.newTemp();

            ctx.emit(t + " = " + l + " - " + r);
            return t;
        }

        @Override
        public String visit(TimesExpression n, CgCtx ctx) {
            String l = n.f0.accept(this, ctx);
            String r = n.f2.accept(this, ctx);
            String t = ctx.newTemp();

            ctx.emit(t + " = " + l + " * " + r);
            return t;
        }

        @Override
        public String visit(CompareExpression n, CgCtx ctx) {
            String l = n.f0.accept(this, ctx);
            String r = n.f2.accept(this, ctx);
            String t = ctx.newTemp();

            ctx.emit(t + " = " + l + " < " + r);
            return t;
        }

        @Override
        public String visit(NotExpression n, CgCtx ctx) {
            String val = n.f1.accept(this, ctx);
            String one = ctx.newTemp();
            String t   = ctx.newTemp();

            ctx.emit(one + " = 1");
            ctx.emit(t + " = " + one + " - " + val);

            return t;
        }

        @Override
        public String visit(ArrayAllocationExpression n, CgCtx ctx) {
            //new int[size] --> alloc (size+1)*4 bytes, store size at [arr+0]
            String size  = n.f3.accept(this, ctx);
            String tOne  = ctx.newTemp();
            String tLen  = ctx.newTemp();
            String tFour = ctx.newTemp();
            String tBytes= ctx.newTemp();
            String arr   = ctx.newTemp();

            ctx.emit(tOne   + " = 1");
            ctx.emit(tLen   + " = " + size + " + " + tOne);
            ctx.emit(tFour  + " = 4");
            ctx.emit(tBytes + " = " + tLen + " * " + tFour);
            ctx.emit(arr    + " = alloc(" + tBytes + ")");
            ctx.emit("[" + arr + "+0] = " + size);

            return arr;
        }

        @Override
        public String visit(ArrayLookup n, CgCtx ctx) {
            //a[i] --> load from [a + (i*4+4)]
            String arr = n.f0.accept(this, ctx);
            String idx = n.f2.accept(this, ctx);
            String tFour = ctx.newTemp();
            String tScale = ctx.newTemp();
            String tOff = ctx.newTemp();
            String tAddr = ctx.newTemp();
            String tVal = ctx.newTemp();
            String len = ctx.newTemp();
            String tZero = ctx.newTemp();
            String tNegCheck = ctx.newTemp();
            String tLenCheck = ctx.newTemp();
            String lblOk1 = ctx.newLabel();
            String lblOk2 = ctx.newLabel();
            String lblErr = ctx.newLabel();

            //if idx < 0 --> err
            //if idx >= len --> err 
            ctx.emit(len + " = [" + arr + "+0]");
            ctx.emit(tZero + " = 0");
            ctx.emit(tNegCheck + " = " + idx + " < " + tZero);
            ctx.emit("if0 " + tNegCheck + " goto " + lblOk1);
            ctx.emit("error(\"array index out of bounds\")");
            ctx.emitLabel(lblOk1);
            ctx.emit(tLenCheck + " = " + idx + " < " + len);
            ctx.emit("if0 " + tLenCheck + " goto " + lblErr);
            ctx.emit("goto " + lblOk2);
            ctx.emitLabel(lblErr);
            ctx.emit("error(\"array index out of bounds\")");
            ctx.emitLabel(lblOk2);

            ctx.emit(tFour + " = 4");
            ctx.emit(tScale + " = " + idx + " * " + tFour);
            ctx.emit(tOff + " = " + tScale + " + " + tFour);
            ctx.emit(tAddr + " = " + arr + " + " + tOff);
            ctx.emit(tVal + " = [" + tAddr + "+0]");

            return tVal;
        }

        @Override
        public String visit(ArrayLength n, CgCtx ctx) {
            //a.length --> [a+0]
            String arr = n.f0.accept(this, ctx);
            String t   = ctx.newTemp();
            ctx.emit(t + " = [" + arr + "+0]");
            return t;
        }

        @Override
        public String visit(ArrayAssignmentStatement n, CgCtx ctx) {
            //a[i] = v
            String arrName = n.f0.f0.tokenImage;
            String arr;
            if (ctx.locals.contains(arrName)) {
                arr = arrName;
            } 
            else {
                // int offset = coffsets.get(ctx.cls).get(arrName);
                String dc = ctx.cls;
                while (dc != null && !(cflds.containsKey(dc) && cflds.get(dc).containsKey(arrName))) {
                    dc = clparent.get(dc);
                }
                int offset = coffsets.get(ctx.cls).get(dc + "_" + arrName);
                arr = ctx.newTemp();
                ctx.emit(arr + " = [this+" + offset + "]");
            }

            String idx  = n.f2.accept(this, ctx);
            String val  = n.f5.accept(this, ctx);

            String len = ctx.newTemp();
            String tZero = ctx.newTemp();
            String tNegCheck = ctx.newTemp();
            String tLenCheck = ctx.newTemp();
            String lblOk1 = ctx.newLabel();
            String lblOk2 = ctx.newLabel();
            String lblErr = ctx.newLabel();

            ctx.emit(len + " = [" + arr + "+0]");
            ctx.emit(tZero + " = 0");
            ctx.emit(tNegCheck + " = " + idx + " < " + tZero);
            ctx.emit("if0 " + tNegCheck + " goto " + lblOk1);
            ctx.emit("error(\"array index out of bounds\")");
            ctx.emitLabel(lblOk1);
            ctx.emit(tLenCheck + " = " + idx + " < " + len);
            ctx.emit("if0 " + tLenCheck + " goto " + lblErr);
            ctx.emit("goto " + lblOk2);
            ctx.emitLabel(lblErr);
            ctx.emit("error(\"array index out of bounds\")");
            ctx.emitLabel(lblOk2);

            String tFour  = ctx.newTemp();
            String tScale = ctx.newTemp();
            String tOff   = ctx.newTemp();
            String tAddr  = ctx.newTemp();

            ctx.emit(tFour  + " = 4");
            ctx.emit(tScale + " = " + idx + " * " + tFour);
            ctx.emit(tOff   + " = " + tScale + " + " + tFour);
            ctx.emit(tAddr  + " = " + arr + " + " + tOff);
            ctx.emit("[" + tAddr + "+0] = " + val);
            return null;
        }



    }







    
    public static void main(String[] args) throws Exception {
        Goal goal = new MiniJavaParser(System.in).Goal();
        goal.accept(new fpVisitor(), null);
        validHierarch();
        computeLayout();
        // //delete:
        // System.out.println("Layout OK");
        // for (String cls : cvtable.keySet()) {
        //     System.out.println(cls + " vtable: " + cvtable.get(cls));
        //     System.out.println(cls + " offsets: " + coffsets.get(cls));
        // }
        StringBuilder sb = new StringBuilder();
        CgCtx ctx = new CgCtx(mainCN, sb);
        goal.accept(new cgVisitor(), ctx);
        emitSkeleton(sb);
        System.out.print(sb);
    }
}





//System.out.println(12); --> tmp0 = 12; print(tmp0);

//cgVisitor == writing pass 
    //walk same AST again as fpVisitor (read)
    //for every node encountered
        //emit sparrow instr into stringBuilder

//need to make multiple temps --> newTemp() --> gen tmp0, then counter tmp1, 2, 3, ...







//alloc the object
//call vtinit to fill vtable
//load vtable ptr from [obj+0]
//load fn ptr from [vtable + slot*4] where slot is fn index
//codegen the args
//call the fn pointer with this + args


// cat > /tmp/Testing.java << 'EOF'
// EOF
 