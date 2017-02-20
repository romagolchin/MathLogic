import java.util.List;

/**
 * Created by Roman on 19/02/2017.
 */
public class Predicate extends LogicOperand {
    String predicateSymbol;
    List<Term> args;

    public Predicate(String predicateSymbol, List<Term> args) {
        this.predicateSymbol = predicateSymbol;
        this.args = args;
    }

    @Override
    public Formula substitute(Variable x, Term t) {
        return null;
    }

    static final String EQ = "=";

}
