/**
 * Created by Roman on 18/02/2017.
 */
public class Variable extends Term {
    private String name;

    public Variable(String name) {
        this.name = name;
    }

    @Override
    public Formula substitute(Variable x, Term t) {
        return t;
    }

}
