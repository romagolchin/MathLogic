/**
 * Created by Roman on 18/02/2017.
 */
public class PredicateExpression extends LogicOperand {
    LogicOperator logicOperator;
    LogicOperand left;
    LogicOperand right;

    public PredicateExpression(LogicOperator logicOperator,
                               LogicOperand left, LogicOperand right) {
        this.logicOperator = logicOperator;
        this.left = left;
        this.right = right;
    }

    @Override
    public Formula substitute(Variable x, Term t) {
        return null;
    }

}
