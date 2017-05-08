package node;

import java.util.ArrayList;


/**
 * Created by Roman on 18/02/2017.
 */
public class Var extends Node implements Term {

    public Var(String name) {
        super(name, new ArrayList<>());
        vars.add(name);
        priority = 9;
    }

    public Var(Node toCopy) {
        super(toCopy);
    }

    @Override
    protected Node copy() {
        return new Var(this);
    }

    @Override
    public boolean equals(Object o) {
        return (o != null && (o.getClass() == getClass() && name.equals(((Var) o).getName())
        || o.getClass() != getClass() && o.equals(this)));
    }
}
