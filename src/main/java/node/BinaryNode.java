package node;

import proofs.Arithmetic;
import proofs.PCalculus;

import java.util.ArrayList;
import java.util.Arrays;

/**
 * Created by Roman on 23/02/2017.
 * convenience class for creating nodes with two children
 */
public class BinaryNode extends Node {

    public BinaryNode(String operator, Node left, Node right) {
        super(operator, new ArrayList<>(Arrays.asList(left, right)));
        isBinOperator = true;
    }

    public BinaryNode(Node toCopy) {
        super(toCopy);
    }

    @Override
    public Node copy() {
        return new BinaryNode(this);
    }

    public Node getLeft() {
        return children.get(0);
    }

    public Node getRight() {
        return children.get(1);
    }

    @Override
    public String toString() {
        if (this instanceof Eq && getLeft().equals(getRight())) {
//            System.err.println(getLeft() + " " + getRight());
        }
        String ls = getLeft().priority < priority ? "(" + getLeft().toString() + ")" : getLeft().toString();
        String rs = getRight().priority < priority ? "(" + getRight().toString() + ")" : getRight().toString();
        return ls + name + rs;
    }

    public static BinaryNode newBinaryNode(String op, Node left, Node right) {
        if (op.equals(PCalculus.OR))
            return new Or(left, right);
        else if (op.equals(PCalculus.AND))
            return new And(left, right);
        else if (op.equals(Arithmetic.ADD))
            return new Add(left, right);
        else
            return new Mul(left, right);
    }

}
