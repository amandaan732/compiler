import java.util.*; //scanner https://docs.oracle.com/en/java/javase/21/docs/api/java.base/java/util/Scanner.html#hasNext()
public class Parse {
    static List<String> tokens;
    static int pos = 0;

    public static void main(String[] args) {
        //scan inp and put into tokens
        Scanner scanner = new Scanner(System.in);
        tokens = new ArrayList<>();
        while (scanner.hasNext()) {
            tokens.add(scanner.next());
        }
        pos = 0;

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

    //diff rules for S L E --> diff fn
    static void parseS() {
        System.out.println("parsing start");
        throw new RuntimeException("not implemented yet");
    }

    static void parseL() {
       throw new RuntimeException("not implemented yet");
    }

    static void parseE() {
       throw new RuntimeException("not implemented yet");
    }
}