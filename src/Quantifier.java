/**
 * Created by Roman on 19/02/2017.
 */
public class Quantifier implements Formula {
    Variable variable;
    QuantifierType type;
    Formula formula;

    public Quantifier(QuantifierType type, Variable variable, Formula formula) {
        this.variable = variable;
        this.type = type;
        this.formula = formula;
    }

    @Override
    public Formula substitute(Variable x, Term t) {
        return null;
    }

    enum QuantifierType {
        FOR_ALL, EXISTS
    }

}
