package node;

import proofs.PCalculus;

/**
 * @author Roman Golchin (romagolchin@gmail.com)
 */
public class Or extends BinaryNode {
    public Or(Node left, Node right) {
        super(PCalculus.OR, left, right);
        priority = 1;
        associativity = Associativity.L;
    }

    public Or(Node toCopy) {
        super(toCopy);
    }

    @Override
    public Node copy() {
        return new Or(this);
    }
}
