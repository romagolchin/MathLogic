package node;

import proofs.PCalculus;

import java.util.ArrayList;
import java.util.Collections;

/**
 * Created by Roman on 24/02/2017.
 */
public class Neg extends Node {
    public Neg(Node child) {
        super(PCalculus.NOT, new ArrayList<>(Collections.singletonList(child)));
        priority = 3;
    }

    public Neg(Node toCopy, boolean x) {
        super(toCopy);
    }
}
