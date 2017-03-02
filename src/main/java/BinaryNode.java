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
    protected Node copy() {
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
        String ls = getLeft().priority < priority ? "(" + getLeft().toString() + ")" : getLeft().toString();
        String rs = getRight().priority < priority ? "(" + getRight().toString() + ")" : getRight().toString();
        return ls + name + rs;
    }
}
