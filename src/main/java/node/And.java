package node;

import proofs.PCalculus;

import static node.BinaryNode.Associativity.L;

/**
 * Created by Roman on 24/02/2017.
 */
public class And extends BinaryNode {
    public And(Node left, Node right) {
        super(PCalculus.AND, left, right);
        priority = 2;
        associativity = L;
    }

    private And(Node toCopy) {
        super(toCopy);
    }


    @Override
    public Node copy() {
        return new And(this);
    }
}
