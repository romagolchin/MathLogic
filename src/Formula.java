
/**
 * Created by Roman on 18/02/2017.
 */
public interface Formula {
    Formula substitute(Variable x, Term t);

    default void generalize() {
        Equation eq = new Equation(new Zero(), new Zero());
        PredicateExpression closedFormula = new PredicateExpression(
                LogicOperator.IMPL, eq,
                new PredicateExpression(LogicOperator.IMPL, eq, eq));
        String [] proof = {  closedFormula.toString(),
        };
    }
}
