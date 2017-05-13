package proofs;

import java.util.Collections;

/**
 * @author Roman Golchin (romagolchin@gmail.com)
 */
public class Util {
    public static <T> Iterable<T> nullCheck(Iterable<T> ts) {
        return ts == null ? Collections.emptySet() : ts;
    }
}
