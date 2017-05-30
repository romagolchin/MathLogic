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

    enum Associativity {
        L, R, N
    }

    protected Associativity associativity;

    public BinaryNode(String operator, Node left, Node right) {
        super(operator, new ArrayList<>(Arrays.asList(left, right)));
        isBinOperator = true;
    }

    public BinaryNode(Node toCopy) {
        super(toCopy);
        if (toCopy instanceof BinaryNode) {
            BinaryNode binaryNode = (BinaryNode) toCopy;
            associativity = binaryNode.associativity;
        }
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


    String bracify(String s) {
        return "(" + s + ")";
    }

    @Override
    public String toString() {
        String rs = getRight().toString();
        String ls = getLeft().toString();
        if (getLeft().priority < priority)
            ls = bracify(ls);
        if (getRight().priority < priority)
            rs = bracify(rs);
        if (getLeft().priority == priority && (associativity == Associativity.R || associativity == Associativity.N))
            ls = bracify(ls);
        if (getRight().priority == priority && (associativity == Associativity.L || associativity == Associativity.N))
            rs = bracify(rs);
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
