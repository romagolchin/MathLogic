/**
 * Created by Roman on 24/02/2017.
 */
public class Impl extends BinaryNode {
    public Impl(Node left, Node right) {
        super(PredicateCalculus.IMPL, left, right);
        priority = 0;
    }

    public Impl(Node toCopy) {
        super(toCopy);
    }

    @Override
    protected Node copy() {
        return new Impl(this);
    }

    @Override
    public String toString() {
        String ls = getLeft().toString();
        if (getLeft().priority <= priority) {
            ls = "(" + ls + ")";
        }
        return ls + name + getRight().toString();
    }
}
