import minijava.syntaxtree.*;
import minijava.visitor.*;
import minijava.MiniJavaParser;
import java.util.*;

public class Typecheck {
    //className -> parent class name (null = no parent), field name --> string, method name --> method info
    static String mainClassName;
    static Map<String, String> classParent = new LinkedHashMap<>();
    static Map<String, Map<String, String>> classFields = new HashMap<>();
    static Map<String, Map<String, MethodInfo>> classMethods = new HashMap<>();

    static class MethodInfo {
        List<String> paramNames = new ArrayList<>();
        List<String> paramTypes = new ArrayList<>();
        String returnType;
    }

    static void error() {
        throw new RuntimeException("type error");
    }

    public static void main(String[] args) {
        try {
            Goal goal = new MiniJavaParser(System.in).Goal();
            collectSymbols(goal);
            validateStructure();
            typeCheckGoal(goal);
            System.out.println("Program type checked successfully");
        } catch (Exception e) {
            System.out.println("Type error");
        }
    }

    //pass1; collect each class name/field/sig
    static void collectSymbols(Goal g) {
        //register main class --> no fields or user-callable methods
        String mainName = g.f0.f1.f0.tokenImage;
        mainClassName = mainName;
        classParent.put(mainName, null);
        classFields.put(mainName, new LinkedHashMap<>());
        classMethods.put(mainName, new LinkedHashMap<>());

        //now regis all the other classes
        for (Enumeration<Node> e = g.f1.elements(); e.hasMoreElements(); ) {
            TypeDeclaration td = (TypeDeclaration) e.nextElement();
            if (td.f0.choice instanceof ClassDeclaration) {
                collectClass((ClassDeclaration) td.f0.choice);
            }
            else {
                collectClassExtends((ClassExtendsDeclaration) td.f0.choice);
            }
        }
    }

    static void collectClass(ClassDeclaration d) {
        String name = d.f1.f0.tokenImage;
        if (classParent.containsKey(name)) { //dup class name
            error(); 
        }

        classParent.put(name, null);

        Map<String, String> fields = new LinkedHashMap<>();
        for (Enumeration<Node> e = d.f3.elements(); e.hasMoreElements(); ) {
            VarDeclaration vd = (VarDeclaration) e.nextElement();
            String fname = vd.f1.f0.tokenImage;
            if (fields.containsKey(fname)) { //dup field
                error(); 
            }
            fields.put(fname, typeToString(vd.f0));
        }

        Map<String, MethodInfo> methods = new LinkedHashMap<>();
        for (Enumeration<Node> e = d.f4.elements(); e.hasMoreElements(); ) {
            MethodDeclaration md = (MethodDeclaration) e.nextElement();
            String mname = md.f2.f0.tokenImage;
            if (methods.containsKey(mname)) { //duplicate method
                error();
            } 
            methods.put(mname, collectMethodInfo(md));
        }

        classFields.put(name, fields);
        classMethods.put(name, methods);
    }

    static void collectClassExtends(ClassExtendsDeclaration d) {
        String name   = d.f1.f0.tokenImage;
        String parent = d.f3.f0.tokenImage;
        if (classParent.containsKey(name)) {
            error();
        }

        classParent.put(name, parent);

        Map<String, String> fields = new LinkedHashMap<>();
        for (Enumeration<Node> e = d.f5.elements(); e.hasMoreElements(); ) {
            VarDeclaration vd = (VarDeclaration) e.nextElement();
            String fname = vd.f1.f0.tokenImage;
            if (fields.containsKey(fname)) {
                error();   
            }
            fields.put(fname, typeToString(vd.f0));
        }

        Map<String, MethodInfo> methods = new LinkedHashMap<>();
        for (Enumeration<Node> e = d.f6.elements(); e.hasMoreElements(); ) {
            MethodDeclaration md = (MethodDeclaration) e.nextElement();
            String mname = md.f2.f0.tokenImage;
            if (methods.containsKey(mname)) error(); 
            methods.put(mname, collectMethodInfo(md));
        }

        classFields.put(name, fields);
        classMethods.put(name, methods);
    }

    static MethodInfo collectMethodInfo(MethodDeclaration md) {
        MethodInfo info = new MethodInfo();
        info.returnType = typeToString(md.f1);

        if (md.f4.present()) {
            FormalParameterList fpl = (FormalParameterList) md.f4.node;
            //first param
            info.paramNames.add(fpl.f0.f1.f0.tokenImage);
            info.paramTypes.add(typeToString(fpl.f0.f0));
            //remaining params
            for (Enumeration<Node> e = fpl.f1.elements(); e.hasMoreElements(); ) {
                FormalParameterRest fpr = (FormalParameterRest) e.nextElement();
                info.paramNames.add(fpr.f1.f1.f0.tokenImage);
                info.paramTypes.add(typeToString(fpr.f1.f0));
            }
        }
        return info;
    }


    //validate class hierarchy
    static void validateStructure() {
        for (Map.Entry<String, String> e : classParent.entrySet()) { //parent named in "extends" must == declared class
            String parent = e.getValue();
            if (parent != null && !classParent.containsKey(parent)) {
                error();
            }
        }

        for (String cls : classParent.keySet()) { //inheritance == acrylic (walk each class' parent chain)
            Set<String> visited = new HashSet<>();
            String cur = cls;
            while (cur != null) {
                if (!visited.add(cur)) { //if saw this class twice == cycle
                    error();   
                }
                cur = classParent.get(cur);
            }
        }

        for (String cls : classParent.keySet()) { //all class-typed names used in fld/mtd decl have to exist
            for (String t : classFields.get(cls).values()) {
                validateTypeRef(t);
            }
            for (MethodInfo m : classMethods.get(cls).values()) {
                validateTypeRef(m.returnType);
                for (String pt : m.paramTypes) {
                    validateTypeRef(pt);
                }
            }
        }

        for (Map.Entry<String, String> e : classParent.entrySet()) { //no overloading; in parent, sig must == exactly (params&return)
            String cls    = e.getKey();
            String parent = e.getValue();
            if (parent == null) continue;
            for (Map.Entry<String, MethodInfo> me : classMethods.get(cls).entrySet()) {
                MethodInfo parentSig = lookupMethod(parent, me.getKey());
                if (parentSig != null && !signaturesMatch(me.getValue(), parentSig))
                    error();
            }
        }
    }

    //exact match on param + return types&order
    static boolean signaturesMatch(MethodInfo a, MethodInfo b) { 
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
    static void validateTypeRef(String t) {
        if (t.equals("int") || t.equals("boolean") || t.equals("int[]")) {
            return;
        }
        if (!classParent.containsKey(t)) {
            error();
        }
    }

    //walk up inherit. chain looking for methodName --> null = not found
    static MethodInfo lookupMethod(String cls, String mname) {
        if (cls == null || !classParent.containsKey(cls)) {
            return null;
        }
        MethodInfo m = classMethods.get(cls).get(mname);
        if (m != null) {
            return m;
        }
        return lookupMethod(classParent.get(cls), mname);
    }


    //typ chk all mtd/main bodies
    static void typeCheckGoal(Goal g) {
        typeCheckMain(g.f0);
        for (Enumeration<Node> e = g.f1.elements(); e.hasMoreElements();) {
            TypeDeclaration td = (TypeDeclaration) e.nextElement();
            if (td.f0.choice instanceof ClassDeclaration) {
                typeCheckClass((ClassDeclaration) td.f0.choice);
            }
            else {
                typeCheckClassExtends((ClassExtendsDeclaration) td.f0.choice);
            }
        }
    }

    //rule 22; main has no "this" (cls = null) --> locals must be distinct
    static void typeCheckMain(MainClass mc) {
        Map<String, String> env = new LinkedHashMap<>();
        Set<String> seen = new HashSet<>();
        seen.add(mc.f6.tokenImage); //main's array param (e.g. "a") == in scope
        for (Enumeration<Node> e = mc.f14.elements(); e.hasMoreElements();) {
            VarDeclaration vd = (VarDeclaration) e.nextElement();
            String name = vd.f1.f0.tokenImage;
            if (!seen.add(name)) error(); //dup local var
            String t = typeToString(vd.f0);
            validateTypeRef(t);
            env.put(name,t);
        }
        for (Enumeration<Node> e = mc.f15.elements(); e.hasMoreElements();) {
            checkStmt((Statement) e.nextElement(), env,null);
        }
    }

    static void typeCheckClass(ClassDeclaration d) {
        String cls = d.f1.f0.tokenImage;
        for (Enumeration<Node> e = d.f4.elements(); e.hasMoreElements();) {
            typeCheckMethod((MethodDeclaration) e.nextElement(), cls);
        }
    }

    static void typeCheckClassExtends(ClassExtendsDeclaration d) {
        String cls = d.f1.f0.tokenImage;
        for (Enumeration<Node> e = d.f6.elements(); e.hasMoreElements();) {
            typeCheckMethod((MethodDeclaration) e.nextElement(), cls);
        }
    }

    //r25; env = fields(C)*params*locals; params+locals pairwise distinct
    static void typeCheckMethod(MethodDeclaration md, String cls) {
        MethodInfo info = classMethods.get(cls).get(md.f2.f0.tokenImage);
        //start with all inherited + own fields
        Map<String, String> env = new LinkedHashMap<>(getAllFields(cls));
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
            if (!paramAndLocals.add(name)) { //clash w/ param or diff local
                error();
            }
            String t = typeToString(vd.f0);
            validateTypeRef(t);
            env.put(name, t);
        }

        for (Enumeration<Node> e = md.f8.elements(); e.hasMoreElements();) {
            checkStmt((Statement) e.nextElement(), env, cls);
        }

        String retType = checkExpr(md.f10, env, cls); //ret expr === decl ret type!
        if (!isSubtype(retType, info.returnType)) {
            error();
        }
    }

    //add one formal parameter --> enforces distinctness
    static void addParam(FormalParameter fp, Map<String, String> env, Set<String> seen) {
        String name = fp.f1.f0.tokenImage;
        if (!seen.add(name)) {
            error();
        }
        String t = typeToString(fp.f0);
        validateTypeRef(t);
        env.put(name,t);
    }

    //stmts (r26-31)
    static void checkStmt(Statement stmt, Map<String, String> env, String cls) {
        Node s = stmt.f0.choice;

        if (s instanceof Block) {
            for (Enumeration<Node> e = ((Block) s).f1.elements(); e.hasMoreElements();) {
                checkStmt((Statement) e.nextElement(), env, cls);
            }
        } 
        else if (s instanceof AssignmentStatement) { //r27; id = e
            AssignmentStatement as = (AssignmentStatement) s;
            String varName = as.f0.f0.tokenImage;
            if (!env.containsKey(varName)) {
                error();
            }
            String rhs = checkExpr(as.f2, env, cls);
            if (!isSubtype(rhs, env.get(varName))) { //rhs type <= lhs type
                error(); 
            }
        } 
        else if (s instanceof ArrayAssignmentStatement) { // r28; id[e1] = e2
            ArrayAssignmentStatement aas = (ArrayAssignmentStatement) s;
            String varName = aas.f0.f0.tokenImage;
            if (!env.containsKey(varName) || !env.get(varName).equals("int[]")) {
                error();
            }
            if (!checkExpr(aas.f2, env, cls).equals("int")) { //ind must be int
                error(); 
            }
            if (!checkExpr(aas.f5, env, cls).equals("int")) { //val must be int
                error(); 
            }
        } 
        else if (s instanceof IfStatement) {  //r29
            IfStatement is = (IfStatement) s;
            if (!checkExpr(is.f2, env, cls).equals("boolean")) {
                error();
            }
            checkStmt(is.f4, env, cls);
            checkStmt(is.f6, env, cls);
        } 
        else if (s instanceof WhileStatement) { //r30
            WhileStatement ws = (WhileStatement) s;
            if (!checkExpr(ws.f2, env, cls).equals("boolean")) {
                error();
            }
            checkStmt(ws.f4, env, cls);
        } 
        else if (s instanceof PrintStatement) { //r31; only int
            if (!checkExpr(((PrintStatement) s).f2, env, cls).equals("int")) {
                error();
            }
        }
    }

    //exprs (r32-39)
    static String checkExpr(Expression expr, Map<String, String> env, String cls) {
        Node e = expr.f0.choice;

        if (e instanceof AndExpression) { //r32; bool && bool -> bool
            AndExpression ae = (AndExpression) e;
            if (!checkPrimary(ae.f0, env, cls).equals("boolean")) {
                error();
            }
            if (!checkPrimary(ae.f2, env, cls).equals("boolean")) {
                error();
            }
            return "boolean";
        } 
        else if (e instanceof CompareExpression) { //r33; int < int -> bool
            CompareExpression ce = (CompareExpression) e;
            if (!checkPrimary(ce.f0, env, cls).equals("int")) {
                error();
            }
            if (!checkPrimary(ce.f2, env, cls).equals("int")) {
                error();
            }
            return "boolean";
        } 
        else if (e instanceof PlusExpression) { //r34
            PlusExpression pe = (PlusExpression) e;
            if (!checkPrimary(pe.f0, env, cls).equals("int")) {
                error();
            }
            if (!checkPrimary(pe.f2, env, cls).equals("int")) {
                error();
            }
            return "int";
        } 
        else if (e instanceof MinusExpression) { //r35
            MinusExpression me = (MinusExpression) e;
            if (!checkPrimary(me.f0, env, cls).equals("int")) {
                error();
            }
            if (!checkPrimary(me.f2, env, cls).equals("int")) {
                error();
            }
            return "int";
        } 
        else if (e instanceof TimesExpression) {  //rule 36
            TimesExpression te = (TimesExpression) e;
            if (!checkPrimary(te.f0, env, cls).equals("int")) {
                error();
            }
            if (!checkPrimary(te.f2, env, cls).equals("int")) {
                error();
            }
            return "int";
        } 
        else if (e instanceof ArrayLookup) { //r37; int[][int] -> int
            ArrayLookup al = (ArrayLookup) e;
            if (!checkPrimary(al.f0, env, cls).equals("int[]")) {
                error();
            }
            if (!checkPrimary(al.f2, env, cls).equals("int")) {
                error();
            }
            return "int";
        } 
        else if (e instanceof ArrayLength) { //r38; int[].length -> int
            if (!checkPrimary(((ArrayLength) e).f0, env, cls).equals("int[]")) {
                error();
            }
            return "int";
        } 
        else if (e instanceof MessageSend) { //r39
            return checkMessageSend((MessageSend) e, env, cls);
        } 
        else { //prim expr
            return checkPrimary((PrimaryExpression) e, env, cls);
        }
    }

    //r39 cont.; p.id(e1,...,en)
    static String checkMessageSend(MessageSend ms, Map<String, String> env, String cls) {
        String receiverType = checkPrimary(ms.f0, env, cls);
        if (!classParent.containsKey(receiverType)) { //must == class; != primitive
            error();   
        }

        String mname = ms.f2.f0.tokenImage;
        MethodInfo method = lookupMethod(receiverType, mname);
        if (method == null) { //mtd not found in hierarch.
            error();  
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

        if (argTypes.size() != method.paramTypes.size()) { //arity has to match
            error();  
        }
        for (int i = 0; i < argTypes.size(); i++) {
            if (!isSubtype(argTypes.get(i), method.paramTypes.get(i))) {
                error();
            }
        }

        return method.returnType;
    }

    //prim. expr. (r40-48)
    static String checkPrimary(PrimaryExpression p, Map<String, String> env, String cls) {
        Node n = p.f0.choice;

        if (n instanceof IntegerLiteral) { //r40
            return "int";    
        }
        if (n instanceof TrueLiteral) { //r41
            return "boolean"; 
        }
        if (n instanceof FalseLiteral) { //r42
            return "boolean";
        }

        if (n instanceof Identifier) { //r43; look up in env   
            String name = ((Identifier) n).f0.tokenImage;
            if (!env.containsKey(name)) {
                error();
            }
            return env.get(name);
        }

        if (n instanceof ThisExpression) { //r44; illegal in main    
            if (cls == null) {
                error();
            }
            return cls;
        }

        if (n instanceof ArrayAllocationExpression) {  // r45; new int[e]
            if (!checkExpr(((ArrayAllocationExpression) n).f3, env, cls).equals("int")) {
                error();
            }
            return "int[]";
        }

        if (n instanceof AllocationExpression) { //r46; new id()
            String newCls = ((AllocationExpression) n).f1.f0.tokenImage;
            if (!classParent.containsKey(newCls) || newCls.equals(mainClassName)) {
                error();
            }
            return newCls;
        }

        if (n instanceof NotExpression) { //r47; !e
            if (!checkExpr(((NotExpression) n).f1, env, cls).equals("boolean")) {
                error();
            }
            return "boolean";
        }

        if (n instanceof BracketExpression) {  //r48; (e)    
            return checkExpr(((BracketExpression) n).f1, env, cls);
        }

        error(); //unreachable (i believe)
        return null;
    }





//helps
    static String typeToString(Type t) {
        Node n = t.f0.choice;
        if (n instanceof ArrayType) {
            return "int[]";
        }
        if (n instanceof BooleanType) {
            return "boolean";
        }
        if (n instanceof IntegerType) {
            return "int";
        }
        return ((Identifier) n).f0.tokenImage; //class type
    }

    //t1 <= t2 --> reflexive + transitive closure of "extends" --> rules 1-3
    //prim only subtype themselves; int[] only subtypes itself
    static boolean isSubtype(String t1, String t2) {
        if (t1 == null || t2 == null) {
            return false;
        }
        if (t1.equals(t2)) {
            return true;
        }
        //walk up inher. chain
        String parent = classParent.get(t1); //null == primitives or root class
        if (parent == null) {
            return false;
        }
        return isSubtype(parent, t2);
    }

    //returns all fields visible in cls (parent fields first, own fields override) --> rules 14-15
    static Map<String, String> getAllFields(String cls) {
        Map<String, String> result = new LinkedHashMap<>();
        if (cls == null) {
            return result;
        }
        String parent = classParent.get(cls);
        if (parent != null) {
            result.putAll(getAllFields(parent));
        }
        result.putAll(classFields.get(cls)); //own fields shadow parent fields
        return result;
    }
}


