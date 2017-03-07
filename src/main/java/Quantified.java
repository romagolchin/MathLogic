import java.util.ArrayList;
import java.util.Collections;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Created by Roman on 23/02/2017.
 */
public class Quantified extends Node {
    protected String variable;

    public String getVariable() {
        return variable;
    }

    public Node getOperand() {
        return children.get(0);
    }

    public Quantified(Node toCopy) {
        super(toCopy);
        if (toCopy instanceof Quantified) {
            variable = ((Quantified) toCopy).variable;
        }
    }

    @Override
    protected Node copy() {
        return new Quantified(this);
    }

    public Quantified(String type, String variable, Node formula) {
        super(type, new ArrayList<>(Collections.singleton(formula)));
        Matcher matcher = Pattern.compile("[a-z][0-9]*").matcher(variable);
        if (!matcher.matches())
            throw new IllegalArgumentException("variable name " + variable + " is not valid");
        this.variable = variable;
    }

    @Override
    public String toString() {
        return name + variable + "(" + children.get(0) + ")";
    }
}
