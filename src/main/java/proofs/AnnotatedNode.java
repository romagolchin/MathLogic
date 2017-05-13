package proofs;

import node.Node;

/**
 * @author Roman Golchin (romagolchin@gmail.com)
 */
class AnnotatedNode {
    Node node;
    ProofType type;

    public AnnotatedNode(Node node, ProofType type) {
        this.node = node;
        this.type = type;
    }

    public Node getNode() {
        return node;
    }

    public ProofType getType() {
        return type;
    }

    public static AnnotatedNode assumption(Node node) {
        return new AnnotatedNode(node, new ProofType.Assumption());
    }
}
