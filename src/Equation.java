import java.util.ArrayList;

/**
 * Created by Roman on 19/02/2017.
 */
public class Equation extends Predicate {
    ArithmeticOperation left;
    ArithmeticOperation right;

    public Equation(ArithmeticOperation left, ArithmeticOperation right) {
        super(EQ, new ArrayList<>());
        this.left = left;
        this.right = right;
    }

    @Override
    public String toString() {
        return left.toString() + EQ + right.toString();
    }
}
