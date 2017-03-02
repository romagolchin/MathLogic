
import java.util.ArrayList;
import java.util.Collections;


/**
 * Created by Roman on 24/02/2017.
 */
public class Inc extends Node implements Term, Calculable {
    int number;


    public Inc(Node node, int number) {
        super(FormalArithmetic.INC,
                new ArrayList<>(Collections.singleton(node)));
        this.number = number;
        if (node instanceof Inc) {
            this.number += ((Inc) node).number;
            children = new ArrayList<>(((Inc) node).children);
        }
    }

    public Inc(Node node) {
        this(node, 1);
    }


    // last parameter is merely to tell copy constructor from other constructors
    public Inc(Node toCopy, boolean x) {
        super(toCopy);
        if (toCopy instanceof Inc)
            number = ((Inc) toCopy).number;
    }

    @Override
    protected Node copy() {
        return new Inc(this, true);
    }

    @Override
    public String toString() {
        Node operand = children.get(0);
        StringBuilder builder = new StringBuilder();
        for (int i = 0; i < number; i++)
            builder.append(FormalArithmetic.INC);
        return operand instanceof Var ? operand + builder.toString() :
                "(" + operand + ")" + builder;
    }

    @Override
    public Node calculate() {
        if (isCalculated())
            return copy();
        else {
            Node resOperand = ((Calculable) getOperand()).calculate();
            if (resOperand != null) {
                for (int i = 1; i <= number; ++i) {
                    System.out.println(new Eq(new Inc(getOperand(), i),
                            new Inc(resOperand, i)));
                }

                return new Inc(resOperand, number);
            }
        }
        return null;
    }

    public Node getOperand() {
        return children.get(0);
    }

    @Override
    public boolean equals(Object o) {
        return super.equals(o) || (number == 0 && getOperand().equals(o));
    }

    @Override
    public boolean isCalculated() {
        return  (equals(FormalArithmetic.Z)
                || getOperand().equals(FormalArithmetic.Z));
    }
}
