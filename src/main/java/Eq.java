
/**
 * Created by Roman on 19/02/2017.
 */
public class Eq extends BinaryNode {
    public Eq(Node left, Node right) {
        super(Arithmetic.EQ, left, right);
        priority = 4;
    }

    public Eq reverse() {
        return new Eq(getRight(), getLeft());
    }

    public Eq(Node toCopy) {
        super(toCopy);
    }

    @Override
    protected Node copy() {
        return new Eq(this);
    }
}
