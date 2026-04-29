import minijava.syntaxtree.*;
import minijava.visitor.*;
import minijava.MiniJavaParser;
import java.util.*;

public class Typecheck {
    //class name walsks to the parent class name 
        //null menans theere is no parent
    static String mainCN;
    static Map<String, String> clparent = new LinkedHashMap<>();
    static Map<String, Map<String, String>> cflds = new HashMap<>();
    static Map<String, Map<String, MethodInfo>> cmtds = new HashMap<>();

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
                fields.put(fname, Typecheck.toString(vd.f0));
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
            String name   = n.f1.f0.tokenImage;
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
                fields.put(fname, Typecheck.toString(vd.f0));
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

    public static void main(String[] args) {
        //clear the globalk state and oarse inptu into AST
            //build sym tanle w frist pass ans validate hierarchy
        mainCN = null;
        clparent.clear();
        cflds.clear();
        cmtds.clear();
        try {
            Goal goal = new MiniJavaParser(System.in).Goal();
            goal.accept(new fpVisitor(), null);
            validHierarch();
            goal.accept(new tcVisitor(), null);
            System.out.println("Program type checked successfully");
        } 
        catch (Exception e) {
            // ////debugging delete later
            // e.printStackTrace();
            System.out.println("Type error");
        }
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


    static class tcVisitor extends GJDepthFirst<String, Map<String, String>> {
        String cls = null;

        @Override
        public String visit(Goal n, Map<String, String> env) {
            n.f0.accept(this, env);
            n.f1.accept(this, env);
            return null;
        }

        @Override
        public String visit(MainClass n, Map<String, String> env) {
            Map<String, String> localEnv = new LinkedHashMap<>();
            Set<String> seen = new HashSet<>();
            seen.add(n.f6.tokenImage); //main's array param (e.g. "a") == in scope
            for (Enumeration<Node> e = n.f14.elements(); e.hasMoreElements();) {
                VarDeclaration vd = (VarDeclaration) e.nextElement();
                String name = vd.f1.f0.tokenImage;
                if (!seen.add(name)) {
                    throw new RuntimeException("type error");
                }
                String t = Typecheck.toString(vd.f0);
                primOrCLName(t);
                localEnv.put(name, t);
            }
            for (Enumeration<Node> e = n.f15.elements(); e.hasMoreElements();) {
                ((Statement) e.nextElement()).accept(this, localEnv);
            }
            return null;
        }

        @Override
        public String visit(ClassDeclaration n, Map<String, String> env) {
            cls = n.f1.f0.tokenImage;
            for (Enumeration<Node> e = n.f4.elements(); e.hasMoreElements();) {
                ((MethodDeclaration) e.nextElement()).accept(this, null);
            }
            return null;
        }

        @Override
        public String visit(ClassExtendsDeclaration n, Map<String, String> env) {
            cls = n.f1.f0.tokenImage;
            for (Enumeration<Node> e = n.f6.elements(); e.hasMoreElements();) {
                ((MethodDeclaration) e.nextElement()).accept(this, null);
            }
            return null;
        }

        @Override
        public String visit(MethodDeclaration n, Map<String, String> env) {
            MethodInfo info = cmtds.get(cls).get(n.f2.f0.tokenImage);
            Map<String, String> methodEnv = new LinkedHashMap<>(makeFLDMap(cls));
            Set<String> paramAndLocals = new HashSet<>();
            if (n.f4.present()) {
                FormalParameterList fpl = (FormalParameterList) n.f4.node;
                addParam(fpl.f0, methodEnv, paramAndLocals);
                for (Enumeration<Node> e = fpl.f1.elements(); e.hasMoreElements();) {
                    addParam(((FormalParameterRest) e.nextElement()).f1, methodEnv,paramAndLocals);
                }
            }
            for (Enumeration<Node> e = n.f7.elements(); e.hasMoreElements();) {
                VarDeclaration vd = (VarDeclaration) e.nextElement();
                String name = vd.f1.f0.tokenImage;
                if (!paramAndLocals.add(name)) {
                    throw new RuntimeException("type error");
                }
                String t= Typecheck.toString(vd.f0);
                primOrCLName(t);
                methodEnv.put(name, t);
            }
            for (Enumeration<Node> e = n.f8.elements(); e.hasMoreElements();)
                ((Statement) e.nextElement()).accept(this, methodEnv);
            String retType = n.f10.accept(this, methodEnv);
            if (!isSub(retType, info.returnType)) {
                throw new RuntimeException("type error");
            }
            return null;
        }

        //stmt vis
        @Override
        public String visit(Statement n,Map<String, String> env) {
            return n.f0.accept(this, env);
        }

        @Override
        public String visit(Block n,Map<String, String> env) {
            for (Enumeration<Node> e = n.f1.elements(); e.hasMoreElements();) {
                ((Statement) e.nextElement()).accept(this, env);
            }
            return null;
        }

        @Override
        public String visit(AssignmentStatement n, Map<String, String> env) {
            String varName = n.f0.f0.tokenImage;
            if (!env.containsKey(varName)) {
                throw new RuntimeException("type error");
            }
            String rhs = n.f2.accept(this, env);
            if (!isSub(rhs, env.get(varName))) {
                throw new RuntimeException("type error");
            }
            return null;
        }

        @Override
        public String visit(ArrayAssignmentStatement n,Map<String, String> env) {
            String varName = n.f0.f0.tokenImage;
            if (!env.containsKey(varName) || !env.get(varName).equals("int[]"))
                throw new RuntimeException("type error");
            if (!n.f2.accept(this, env).equals("int")) {
                throw new RuntimeException("type error");
            }
            if (!n.f5.accept(this, env).equals("int")) {
                throw new RuntimeException("type error");
            }
            return null;
        }

        @Override
        public String visit(IfStatement n,Map<String, String> env) {
            if (!n.f2.accept(this, env).equals("boolean")) {
                throw new RuntimeException("type error");
            }
            n.f4.accept(this, env);
            n.f6.accept(this, env);
            return null;
        }

        @Override
        public String visit(WhileStatement n, Map<String, String> env) {
            if (!n.f2.accept(this, env).equals("boolean")) {
                throw new RuntimeException("type error");
            }
            n.f4.accept(this, env);
            return null;
        }

        @Override
        public String visit(PrintStatement n, Map<String, String> env) {
            if (!n.f2.accept(this, env).equals("int")) {
                throw new RuntimeException("type error");
            }
            return null;
        }

        //expr vis
        @Override
        public String visit(Expression n,Map<String, String> env) {
            return n.f0.accept(this, env);
        }

        @Override
        public String visit(AndExpression n,Map<String, String> env) {
            if (!n.f0.accept(this, env).equals("boolean")) {
                throw new RuntimeException("type error");
            }
            if (!n.f2.accept(this, env).equals("boolean")) {
                throw new RuntimeException("type error");
            }
            return "boolean";
        }

        @Override
        public String visit(CompareExpression n, Map<String, String> env) {
            if (!n.f0.accept(this, env).equals("int")) {
                throw new RuntimeException("type error");
            }
            if (!n.f2.accept(this, env).equals("int")) {
                throw new RuntimeException("type error");
            }
            return "boolean";
        }

        @Override
        public String visit(PlusExpression n, Map<String, String> env) {
            if (!n.f0.accept(this, env).equals("int")) {
                throw new RuntimeException("type error");
            }
            if (!n.f2.accept(this, env).equals("int")) {
                throw new RuntimeException("type error");
            }
            return "int";
        }

        @Override
        public String visit(MinusExpression n, Map<String, String> env) {
            if (!n.f0.accept(this, env).equals("int")) {
                throw new RuntimeException("type error");
            }
            if (!n.f2.accept(this, env).equals("int")) {
                throw new RuntimeException("type error");
            }
            return "int";
        }

        @Override
        public String visit(TimesExpression n, Map<String, String> env) {
            if (!n.f0.accept(this, env).equals("int")) {
                throw new RuntimeException("type error");
            }
            if (!n.f2.accept(this, env).equals("int")) {
                throw new RuntimeException("type error");
            }
            return "int";
        }

        @Override
        public String visit(ArrayLookup n, Map<String, String> env) {
            if (!n.f0.accept(this, env).equals("int[]")) {
                throw new RuntimeException("type error");
            }
            if (!n.f2.accept(this, env).equals("int")) {
                throw new RuntimeException("type error");
            }
            return "int";
        }

        @Override
        public String visit(ArrayLength n, Map<String, String> env) {
            if (!n.f0.accept(this, env).equals("int[]")) {
                throw new RuntimeException("type error");
            }
            return "int";
        }

        @Override
        public String visit(MessageSend n, Map<String, String> env) {
            String receiverType = n.f0.accept(this, env);
            if (!clparent.containsKey(receiverType)) {
                throw new RuntimeException("type error");
            }
            String mname = n.f2.f0.tokenImage;
            MethodInfo mtd = findMTD(receiverType, mname);
            if (mtd == null) {
                throw new RuntimeException("type error");
            }
            List<String> argTypes = new ArrayList<>();
            if (n.f4.present()) {
                ExpressionList el = (ExpressionList) n.f4.node;
                argTypes.add(el.f0.accept(this, env));
                for (Enumeration<Node> e = el.f1.elements(); e.hasMoreElements();) {
                    argTypes.add(((ExpressionRest) e.nextElement()).f1.accept(this, env));
                }
            }
            if (argTypes.size() != mtd.paramTypes.size()) {
                throw new RuntimeException("type error");
            }
            for (int i = 0; i < argTypes.size(); i++)
                if (!isSub(argTypes.get(i), mtd.paramTypes.get(i))) {
                    throw new RuntimeException("type error");
                }
            return mtd.returnType;
        }

        //prim expr vis
        @Override
        public String visit(PrimaryExpression n,Map<String, String> env) {
            return n.f0.accept(this, env);
        }
        @Override 
        public String visit(IntegerLiteral n,Map<String, String> env) { 
            return "int"; 
        }
        @Override 
        public String visit(TrueLiteral n,Map<String, String> env) { 
            return "boolean"; 
        }
        @Override 
        public String visit(FalseLiteral n,Map<String, String> env) { 
            return "boolean"; 
        }
        @Override
        public String visit(Identifier n,Map<String, String> env) {
            String name = n.f0.tokenImage;
            if (!env.containsKey(name)) {
                throw new RuntimeException("type error");
            }
            return env.get(name);
        }
        @Override
        public String visit(ThisExpression n, Map<String, String> env) {
            if (cls == null) {
                throw new RuntimeException("type error");
            }
            return cls;
        }

        @Override
        public String visit(ArrayAllocationExpression n, Map<String, String> env) {
            if (!n.f3.accept(this, env).equals("int")) {
                throw new RuntimeException("type error");
            }
            return "int[]";
        }


        @Override
        public String visit(AllocationExpression n, Map<String, String> env) {
            String newCls = n.f1.f0.tokenImage;
            if (!clparent.containsKey(newCls) || newCls.equals(mainCN)) {
                throw new RuntimeException("type error");
            }
            return newCls;
        }

        @Override
        public String visit(NotExpression n, Map<String, String> env) {
            if (!n.f1.accept(this, env).equals("boolean")) {
                throw new RuntimeException("type error");
            }
            return "boolean";
        }
        @Override
        public String visit(BracketExpression n, Map<String, String> env) {
            return n.f1.accept(this, env);
        }
    }





}







// 1) register all the classes (name,field, metd, sig) into maps
// 2) check the hierarchu is legal
//     i) no cycles, no overloeading, valid types
// 3)xheck that all the statmeents, expressions, methods are good
//     a) if you check the method body, then verify that the return expr type is a subtype of decl ret type

// parse-->1st pass-->hierarchy check-->goal-->result





// for f in testcases/hw2/*.java; do
//     expected=$(cat "$f.out")
//     actual=$(gradle -q run < "$f")
//     if [ "$expected" = "$actual" ]; then
//         echo "PASS: $f"
//     else
//         echo "FAIL: $f (expected: $expected, got: $actual)"
//     fi
// done



// ----
// 18 HW2 tests pass locally
// parser imports are allowed
// extra tar contents should be okay acoord. Piazza
// static-state fix --> didnt do anything

// hidden-test-only bug that somehow also causes public tests to fail remotely?
// the official autograder is invoking/building code differently from local Gradle?
// submission-layout expectation not captured by local test?

// So the autograder actually checks the program to see if you use any visitors. Looking at the autograder output it's printing 

// cannot find any visitor being used
// for every test case, so that's why it's passing on gradle pregrade but not on the autograder. You'll need to use the visitor pattern by extending the default visitors instead of calling instanceof.


//fix plan:
// keep:
// global maps (clparent, cflds, cmtds, mainCN)
// validHierarch 
// buildMTD, makeFLDMap, addParam, findMTD, doSigsMatch, primOrCLName, isSub, toString (helpers)
// type checking logic (still same rules)

// change:
// firstPass needs to use visitors --> same logic but inside a visitor class with visit methods
// accept nodes instead of calling checkstmt etc.
// checkStmt, checkExpr, checkPrim, checkMTDCall into one larger tcVisitor 
//     if (s instanceof IfStatement) --> public String visit(IfStatement n, Map<String, String> env)
// firstPass(goal); --> javagoal.accept(new fpVisitor(), null);
// validHierarch(); --> validHierarch();
// tcGoal(goal); --> goal.accept(new tcVisitor(), null);




