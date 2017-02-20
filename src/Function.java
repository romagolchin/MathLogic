import java.util.List;

/**
 * Created by Roman on 19/02/2017.
 */
public class Function extends Term {
    static final String MUL = "*";
    static final String ADD = "+";
    static final String INC = "'";
    static final String ZERO = "0";
    String functionalSymbol;
    List<Term> args;

    public Function(String functionalSymbol, List<Term> args) {
        this.functionalSymbol = functionalSymbol;
        this.args = args;
    }
}
