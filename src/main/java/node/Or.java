package node;

import proofs.PCalculus;

/**
 * @author Roman Golchin (romagolchin@gmail.com)
 */
public class Or extends BinaryNode {
    public Or(Node left, Node right) {
        super(PCalculus.OR, left, right);
    }
}
