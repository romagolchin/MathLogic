import java.util.List;

/**
 * Created by Roman on 19/02/2017.
 */
public abstract class ArithmeticOperation extends Function {
    public ArithmeticOperation(String functionalSymbol, List<Term> args) {
        super(functionalSymbol, args);
    }
    abstract int calculate();

}
