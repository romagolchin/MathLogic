package node;

import com.google.common.collect.ImmutableMap;
import proofs.Arithmetic;
import proofs.PCalculus;

import java.util.ArrayList;
import java.util.Collections;


/**
 * Created by Roman on 24/02/2017.
 */
public class Inc extends Node implements Term, Calculable {
    int number;


    public Inc(Node node, int number) {
        super(Arithmetic.INC,
                new ArrayList<>(Collections.singleton(node)));
        this.number = number;
        if (node instanceof Inc) {
            this.number += ((Inc) node).number;
            children = new ArrayList<>(node.getChildren());
        }
        priority = 7;
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
            builder.append(Arithmetic.INC);
        return operand instanceof Var ? operand + builder.toString() :
                "(" + operand + ")" + builder;
    }

    @Override
    public Node calculate() {
//        System.out.println("Inc " + number);
        if (isCalculated()) {
//            System.out.println("end Inc " + number);
            return copy();
        } else {

            Node resOperand = ((Calculable) getOperand()).calculate();
            if (resOperand != null) {
                for (int i = 1; i <= number; ++i) {
                    PCalculus.MP(Arithmetic.AXIOMS[0].rename(ImmutableMap.of(
                            "a", new Inc(getOperand(), i - 1), "b", new Inc(resOperand, i - 1)
                    )));
//                    System.out.println(new Eq(new Inc(getOperand(), i),
//                            new Inc(resOperand, i)));
                }
//                System.out.println("end Inc " + number);
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
        return (equals(Arithmetic.Z)
                || getOperand().equals(Arithmetic.Z)
//                || getOperand() instanceof Calculable && ((Calculable) getOperand()).isCalculated()
        );
    }

    public static Node create(Node node, int number) {
        return number == 0 ? node : new Inc(node, number);
    }
}
