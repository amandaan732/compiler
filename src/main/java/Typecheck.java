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

    static void firstPass(Goal g) {
        //register the main class, then add it to class' parent w null parent & empty maps for fields and methods
        //loop through all other class declarations 
            //checks if plain class or a class extends and call correct fn
        //pass off details; the acutal fld/mtd collection is somewheer else
        String mainName = g.f0.f1.f0.tokenImage;
        mainCN = mainName;

        clparent.put(mainName, null);
        cflds.put(mainName, new LinkedHashMap<>());
        cmtds.put(mainName, new LinkedHashMap<>());

        //now regis all the other classes
        for (Enumeration<Node> e = g.f1.elements(); e.hasMoreElements(); ) {
            TypeDeclaration td = (TypeDeclaration) e.nextElement();
            if (td.f0.choice instanceof ClassDeclaration) {
                handlePlainCL((ClassDeclaration) td.f0.choice);
            }
            else {
                handleExtnds((ClassExtendsDeclaration) td.f0.choice);
            }
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
            firstPass(goal);
            validHierarch();
            tcGoal(goal);
            System.out.println("Program type checked successfully");
        } 
        catch (Exception e) {
            // ////debugging delete later
            // e.printStackTrace();
            System.out.println("Type error");
        }
    }

    static void handlePlainCL(ClassDeclaration d) {
        String name = d.f1.f0.tokenImage;
        if (clparent.containsKey(name)) { //dup class name
            throw new RuntimeException("type error"); 
        }

        clparent.put(name, null);
        Map<String, String> fields = new LinkedHashMap<>();
        for (Enumeration<Node> e = d.f3.elements(); e.hasMoreElements(); ) {
            VarDeclaration vd = (VarDeclaration) e.nextElement();
            String fname = vd.f1.f0.tokenImage;
            if (fields.containsKey(fname)) { 
                throw new RuntimeException("type error");
            }
            fields.put(fname, toString(vd.f0));
        }
        Map<String, MethodInfo> methods = new LinkedHashMap<>();
        for (Enumeration<Node> e = d.f4.elements(); e.hasMoreElements(); ) {
            MethodDeclaration md = (MethodDeclaration) e.nextElement();
            String mname = md.f2.f0.tokenImage;
            if (methods.containsKey(mname)) { 
                throw new RuntimeException("type error");
            } 
            methods.put(mname, buildMTD(md));
        }
        cflds.put(name, fields);
        cmtds.put(name, methods);
    }

    static void handleExtnds(ClassExtendsDeclaration d) {
        String name   = d.f1.f0.tokenImage;
        String parent = d.f3.f0.tokenImage;
        if (clparent.containsKey(name)) {
            throw new RuntimeException("type error");
        }
        clparent.put(name, parent);
        Map<String, String> fields = new LinkedHashMap<>();
        for (Enumeration<Node> e = d.f5.elements(); e.hasMoreElements(); ) {
            VarDeclaration vd = (VarDeclaration) e.nextElement();
            String fname = vd.f1.f0.tokenImage;
            if (fields.containsKey(fname)) {
                throw new RuntimeException("type error");   
            }
            fields.put(fname, toString(vd.f0));
        }

        Map<String, MethodInfo> methods = new LinkedHashMap<>();
        for (Enumeration<Node> e = d.f6.elements(); e.hasMoreElements(); ) {
            MethodDeclaration md = (MethodDeclaration) e.nextElement();
            String mname = md.f2.f0.tokenImage;
            if (methods.containsKey(mname)){
                throw new RuntimeException("type error");
            }
            methods.put(mname, buildMTD(md));
        }
        cflds.put(name,fields);
        cmtds.put(name,methods);
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


    //typ chk all mtd/main bodies
    static void tcGoal(Goal g) {
        tcMain(g.f0);
        for (Enumeration<Node> e = g.f1.elements(); e.hasMoreElements();) {
            TypeDeclaration td = (TypeDeclaration) e.nextElement();
            if (td.f0.choice instanceof ClassDeclaration) {
                tcCL((ClassDeclaration) td.f0.choice);
            }
            else {
                tcCLExt((ClassExtendsDeclaration) td.f0.choice);
            }
        }
    }

    static void tcMain(MainClass mc) {
        Map<String, String> env = new LinkedHashMap<>();
        Set<String> seen = new HashSet<>();
        seen.add(mc.f6.tokenImage); //main's array param (e.g. "a") == in scope
        for (Enumeration<Node> e = mc.f14.elements(); e.hasMoreElements();) {
            VarDeclaration vd = (VarDeclaration) e.nextElement();
            String name = vd.f1.f0.tokenImage;
            if (!seen.add(name)) {
                throw new RuntimeException("type error");
            } 
            String t = toString(vd.f0);
            primOrCLName(t);
            env.put(name,t);
        }
        for (Enumeration<Node> e = mc.f15.elements(); e.hasMoreElements();) {
            checkStmt((Statement) e.nextElement(), env,null);
        }
    }

    static void tcCL(ClassDeclaration d) {
        String cls = d.f1.f0.tokenImage;
        for (Enumeration<Node> e = d.f4.elements(); e.hasMoreElements();) {
            tcMTD((MethodDeclaration) e.nextElement(), cls);
        }
    }

    static void tcCLExt(ClassExtendsDeclaration d) {
        String cls = d.f1.f0.tokenImage;
        for (Enumeration<Node> e = d.f6.elements(); e.hasMoreElements();) {
            tcMTD((MethodDeclaration) e.nextElement(), cls);
        }
    }

    static void tcMTD(MethodDeclaration md, String cls) {
        MethodInfo info = cmtds.get(cls).get(md.f2.f0.tokenImage);
        Map<String, String> env = new LinkedHashMap<>(makeFLDMap(cls));
        //all params and locals == pairwise distinct
        Set<String> paramAndLocals = new HashSet<>();

        if (md.f4.present()) {
            FormalParameterList fpl = (FormalParameterList) md.f4.node;
            addParam(fpl.f0, env, paramAndLocals);
            for (Enumeration<Node> e = fpl.f1.elements(); e.hasMoreElements();) {
                addParam(((FormalParameterRest) e.nextElement()).f1, env, paramAndLocals);
            }
        }

        for (Enumeration<Node> e = md.f7.elements(); e.hasMoreElements();) {
            VarDeclaration vd = (VarDeclaration) e.nextElement();
            String name = vd.f1.f0.tokenImage;
            if (!paramAndLocals.add(name)) { 
                throw new RuntimeException("type error");
            }
            String t = toString(vd.f0);
            primOrCLName(t);
            env.put(name, t);
        }

        for (Enumeration<Node> e = md.f8.elements(); e.hasMoreElements();) {
            checkStmt((Statement) e.nextElement(), env, cls);
        }

        String retType = checkExpr(md.f10, env, cls); 
        if (!isSub(retType, info.returnType)) {
            throw new RuntimeException("type error");
        }
    }

    //add a formal parameter == enforce uniqueness
    static void addParam(FormalParameter fp, Map<String, String> env, Set<String> seen) {
        String name = fp.f1.f0.tokenImage;
        if (!seen.add(name)) {
            throw new RuntimeException("type error");
        }
        String t = toString(fp.f0);
        primOrCLName(t);
        env.put(name,t);
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
        result.putAll(cflds.get(cls)); //shadow parent fields
        return result;
    }

    //stmts (r26-31)
    static void checkStmt(Statement stmt, Map<String, String> env, String cls) {
        Node s = stmt.f0.choice;

        if (s instanceof Block) {
            for (Enumeration<Node> e = ((Block) s).f1.elements(); e.hasMoreElements();) {
                checkStmt((Statement) e.nextElement(), env, cls);
            }
        } 
        else if (s instanceof AssignmentStatement) {
            AssignmentStatement as = (AssignmentStatement) s;
            String varName = as.f0.f0.tokenImage;
            if (!env.containsKey(varName)) {
                throw new RuntimeException("type error");
            }
            String rhs = checkExpr(as.f2, env, cls);
            if (!isSub(rhs, env.get(varName))) { 
                throw new RuntimeException("type error");
            }
        } 
        else if (s instanceof ArrayAssignmentStatement) { 
            ArrayAssignmentStatement aas = (ArrayAssignmentStatement) s;
            String varName = aas.f0.f0.tokenImage;
            if (!env.containsKey(varName) || !env.get(varName).equals("int[]")) {
                throw new RuntimeException("type error");
            }
            if (!checkExpr(aas.f2, env, cls).equals("int")) { //ind must be int
                throw new RuntimeException("type error");
            }
            if (!checkExpr(aas.f5, env, cls).equals("int")) { //val must be int
                throw new RuntimeException("type error");
            }
        } 
        else if (s instanceof IfStatement) { 
            IfStatement is = (IfStatement) s;
            if (!checkExpr(is.f2, env, cls).equals("boolean")) {
                throw new RuntimeException("type error");
            }
            checkStmt(is.f4, env, cls);
            checkStmt(is.f6, env, cls);
        } 
        else if (s instanceof WhileStatement) { 
            WhileStatement ws = (WhileStatement) s;
            if (!checkExpr(ws.f2, env, cls).equals("boolean")) {
                throw new RuntimeException("type error");
            }
            checkStmt(ws.f4, env, cls);
        } 
        else if (s instanceof PrintStatement) { //r31; only int
            if (!checkExpr(((PrintStatement) s).f2, env, cls).equals("int")) {
                throw new RuntimeException("type error");
            }
        }
    }

    //exprs (r32-39)
    static String checkExpr(Expression expr, Map<String, String> env, String cls) {
        Node e = expr.f0.choice;

        if (e instanceof AndExpression) {
            AndExpression ae = (AndExpression) e;
            if (!checkPrim(ae.f0, env, cls).equals("boolean")) {
                throw new RuntimeException("type error");
            }
            if (!checkPrim(ae.f2, env, cls).equals("boolean")) {
                throw new RuntimeException("type error");
            }
            return "boolean";
        } 
        else if (e instanceof CompareExpression) { 
            CompareExpression ce = (CompareExpression) e;
            if (!checkPrim(ce.f0, env, cls).equals("int")) {
                throw new RuntimeException("type error");
            }
            if (!checkPrim(ce.f2, env, cls).equals("int")) {
                throw new RuntimeException("type error");
            }
            return "boolean";
        } 
        else if (e instanceof PlusExpression) {
            PlusExpression pe = (PlusExpression) e;
            if (!checkPrim(pe.f0, env, cls).equals("int")) {
                throw new RuntimeException("type error");
            }
            if (!checkPrim(pe.f2, env, cls).equals("int")) {
                throw new RuntimeException("type error");
            }
            return "int";
        } 
        else if (e instanceof MinusExpression) { 
            MinusExpression me = (MinusExpression) e;
            if (!checkPrim(me.f0, env, cls).equals("int")) {
                throw new RuntimeException("type error");
            }
            if (!checkPrim(me.f2, env, cls).equals("int")) {
                throw new RuntimeException("type error");
            }
            return "int";
        } 
        else if (e instanceof TimesExpression) { 
            TimesExpression te = (TimesExpression) e;
            if (!checkPrim(te.f0, env, cls).equals("int")) {
                throw new RuntimeException("type error");
            }
            if (!checkPrim(te.f2, env, cls).equals("int")) {
                throw new RuntimeException("type error");
            }
            return "int";
        } 
        else if (e instanceof ArrayLookup) { 
            ArrayLookup al = (ArrayLookup) e;
            if (!checkPrim(al.f0, env, cls).equals("int[]")) {
                throw new RuntimeException("type error");
            }
            if (!checkPrim(al.f2, env, cls).equals("int")) {
                throw new RuntimeException("type error");
            }
            return "int";
        } 
        else if (e instanceof ArrayLength) { 
            if (!checkPrim(((ArrayLength) e).f0, env, cls).equals("int[]")) {
                throw new RuntimeException("type error");
            }
            return "int";
        } 
        else if (e instanceof MessageSend) { //r39
            return checkMTDCall((MessageSend) e, env, cls);
        } 
        else { //prim expr
            return checkPrim((PrimaryExpression) e, env, cls);
        }
    }

    //r39 cont.; p.id(e1,...,en)
    static String checkMTDCall(MessageSend ms, Map<String, String> env, String cls) {
        String receiverType = checkPrim(ms.f0, env, cls);
        if (!clparent.containsKey(receiverType)) { //must == class; CANR be  primitive
            throw new RuntimeException("type error");
        }

        String mname = ms.f2.f0.tokenImage;
        MethodInfo method = findMTD(receiverType, mname);
        if (method == null) { 
            throw new RuntimeException("type error");
        }

        //collect actual arg types
        List<String> argTypes = new ArrayList<>();
        if (ms.f4.present()) {
            ExpressionList el = (ExpressionList) ms.f4.node;
            argTypes.add(checkExpr(el.f0, env, cls));
            for (Enumeration<Node> en = el.f1.elements(); en.hasMoreElements();) {
                argTypes.add(checkExpr(((ExpressionRest) en.nextElement()).f1, env, cls));
            }
        }

        if (argTypes.size() != method.paramTypes.size()) { //arity match
            throw new RuntimeException("type error"); 
        }
        for (int i = 0; i < argTypes.size(); i++) {
            if (!isSub(argTypes.get(i), method.paramTypes.get(i))) {
                throw new RuntimeException("type error");
            }
        }

        return method.returnType;
    }

    static String checkPrim(PrimaryExpression p, Map<String, String> env, String cls) {
        Node node = p.f0.choice;

        if (node instanceof IntegerLiteral) { 
            return "int";    
        }
        if (node instanceof TrueLiteral || node instanceof FalseLiteral) { 
            return "boolean"; 
        }


        if (node instanceof Identifier) {
            String name =((Identifier) node).f0.tokenImage;
            if (!env.containsKey(name)) {
                throw new RuntimeException("type error");
            }
            return env.get(name);
        }

        if (node instanceof ThisExpression) {   
            if (cls==null) {
                throw new RuntimeException("type error");
            }
            return cls;
        }


        if (node instanceof ArrayAllocationExpression) {  
            if (!checkExpr(((ArrayAllocationExpression) node).f3, env, cls).equals("int")) {
                throw new RuntimeException("type error");
            }
            return "int[]";
        }

        if (node instanceof AllocationExpression) { 
            String newCls = ((AllocationExpression) node).f1.f0.tokenImage;
            if (!clparent.containsKey(newCls) || newCls.equals(mainCN)) {
                throw new RuntimeException("type error");
            }
            return newCls;
        }


        if (node instanceof NotExpression) { 
            if (!checkExpr(((NotExpression) node).f1, env, cls).equals("boolean")) {
                throw new RuntimeException("type error");
            }
            return "boolean";
        }

        if (node instanceof BracketExpression) {     
            return checkExpr(((BracketExpression) node).f1, env, cls);
        }


        throw new RuntimeException("type error");
        // return null;
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
// the official autograder is invoking/building your code differently from local Gradle?
// submission-layout expectation not captured by local test?