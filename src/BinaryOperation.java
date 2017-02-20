import com.sun.corba.se.impl.oa.poa.AOMEntry;

import javax.crypto.AEADBadTagException;
import java.util.ArrayList;

/**
 * Created by Roman on 19/02/2017.
 */
public abstract class BinaryOperation extends ArithmeticOperation {

    public BinaryOperation(String symbol, Term left, Term right) {
        super(symbol, new ArrayList<>());
        args = new ArrayList<>(2);
        args.add(left);
        args.add(right);
        this.functionalSymbol = symbol;
    }

    abstract int applyZeroAxiom();

    abstract int applyNonZeroAxiom();

    @Override
    int calculate() {
        Term right = args.get(1);
        if (right instanceof ArithmeticOperation) {
            ArithmeticOperation rightOperand = (ArithmeticOperation) right;
            if (rightOperand.functionalSymbol.equals(ZERO)) {
                return applyZeroAxiom();
            } else {
                return applyNonZeroAxiom();
            }
        }
        return -1;
    }

}
