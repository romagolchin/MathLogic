package node;

import proofs.PCalculus;

import java.util.Collections;

/**
 * @author Roman Golchin (romagolchin@gmail.com)
 */
public class Not extends Node {
    public Not(Node child) {
        super(PCalculus.NOT, Collections.singletonList(child));
    }
}
