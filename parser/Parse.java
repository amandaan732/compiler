import java.util.*; //scanner https://docs.oracle.com/en/java/javase/21/docs/api/java.base/java/util/Scanner.html#hasNext()
public class Parse {
    static List<String> tokens;
    static int pos = 0;

    public static void main(String[] args) {
        //scan inp and put into tokens
        //need to pre-process
        Scanner scanner = new Scanner(System.in);
        tokens = new ArrayList<>();
        // while (scanner.hasNext()) {
        //     tokens.add(scanner.next());
        // }
        // pos = 0;
        String inp = "";
        while (scanner.hasNextLine()) {
            inp += scanner.nextLine() + " ";
        }
        inp = inp.replace("{", " { ");
        inp = inp.replace("}", " } ");
        inp = inp.replace("(", " ( ");
        inp = inp.replace(")", " ) ");
        inp = inp.replace(";", " ; ");
        inp = inp.replace("!", " ! ");
        for (String t : inp.split("\\s+")) {
            if (!t.isEmpty()) tokens.add(t);
        }

        //parse start symbol and react accordingly to kick off 
        try {
            parseS();
            if (pos == tokens.size()) {
                System.out.println("Program parsed successfully");
            } 
            else {
                System.out.println("Parse error");
            }
        } catch (Exception e) {
            System.out.println("Parse error");
        }
    }

    static String justLook() { //only look @ cur token (no consuming it)
        if (pos < tokens.size()) {
            return tokens.get(pos);
        } 
        return "";
    }
    
    static void expect(String token) { //if match consume, else error 
        if (justLook().equals(token)) {
            pos++;
        } else {
            throw new RuntimeException("expected " + token + " but got " + justLook());
        }
    }

    //look at first element to decide what to do:
    static void parseS() {
        String cur = justLook();
        if (cur.equals("{")) {
            //resp for encountering list of statements
            expect("{");
            parseL();
            expect("}");
        }
        else if (cur.equals("System.out.println")) {
            expect("System.out.println");
            expect("(");
            parseE();
            expect(")");
            expect(";");
        }
        else if (cur.equals("if")) {
            expect("if");
            expect("(");
            parseE();
            expect(")");
            parseS();
            expect("else");
            parseS();
        }
        else if (cur.equals("while")) {
            expect("while");
            expect("(");
            parseE();
            expect(")");
            parseS();
        }
        else {
            throw new RuntimeException("S parse error");
        }
    }

    static void parseL() {
        String cur = justLook();
        //either gonna be an S or assume its empty case --> starts with { , print, if, or while to be S L case

        if (cur.equals("{") || cur.equals("System.out.println") || cur.equals("if") || cur.equals("while")) {
            parseS();
            parseL();
        }
        // else {
        //     throw new RuntimeException("L parse error");
        // }
        // System.out.println("L not done yet");
    }

    static void parseE() {
        //true false or ! E --> can be ! ! ! ! ! true , etc.
        String cur = justLook();
        if (cur.equals("true")) {
            expect("true");
        }
        else if (cur.equals("false")) {
            expect("false");
        }
        else if (cur.equals("!")) {
            expect("!");
            parseE();
        }
        else {
            throw new RuntimeException("E parse error");
        }
    }
}