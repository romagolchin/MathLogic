package node;

import proofs.PCalculus;

/**
 * Created by Roman on 24/02/2017.
 */
public class Impl extends BinaryNode {
    public Impl(Node left, Node right) {
        super(PCalculus.IMPL, left, right);
        priority = 0;
        associativity = Associativity.R;
    }

    protected Impl(Node toCopy) {
        super(toCopy);
    }

    @Override
    public Node copy() {
        return new Impl(this);
    }

}
