package proofs;

import node.Node;

import static proofs.Checker.ANN_HYPO;
import static proofs.Checker.ANN_MP;
import static proofs.Checker.ANN_SCHEME;

/**
 * @author Roman Golchin (romagolchin@gmail.com)
 */
public abstract class ProofType {
    static final class MP extends ProofType {
        public MP(Node first) {
            this.first = first;
        }

        public MP(Node first, int firstInd, int secondInd) {
            this.first = first;
            this.firstInd = firstInd;
            this.secondInd = secondInd;
        }

        @Override
        public String toString() {
            return ANN_MP + (firstInd + 1) + ", " + (secondInd + 1);
        }

        Node first;
        int firstInd = -1, secondInd = -1;
    }

    static final class Assumption extends ProofType {
        public Assumption() {
        }

        public Assumption(int i) {
            this.i = i;
        }

        @Override
        public String toString() {
            return ANN_HYPO + (i + 1);
        }

        int i = -1;
    }

    static final class Scheme extends ProofType {
        public Scheme() {
        }

        public Scheme(int i) {
            this.i = i;
        }

        @Override
        public String toString() {
            return ANN_SCHEME + (i + 1);
        }

        int i = -1;
    }

    static final class Forall extends ProofType {
    }

    static final class Exists extends ProofType {
    }

    @Override
    public String toString() {
        return getClass().getSimpleName();
    }
}
