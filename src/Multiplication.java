
/**
 * Created by Roman on 19/02/2017.
 */
public class Multiplication extends BinaryOperation {

    public Multiplication(Term left, Term right) {
        super(MUL, left, right);
    }

    @Override
    int applyZeroAxiom() {

        // x * 0 = 0
        System.out.println(new Equation(
                new Multiplication(new Variable("x"), new Zero()), new Zero()));
        return 0;
    }

    @Override
    int applyNonZeroAxiom() {
        return 0;
    }
}
