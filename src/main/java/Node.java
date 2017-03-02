
import com.sun.istack.internal.Nullable;

import java.util.*;

/**
 * Created by Roman on 20/02/2017.
 */
public class Node {
    protected boolean isBinOperator;
    protected final String name;
    @Nullable
    protected List<Node> children;
    protected Set<String> vars;
    protected int priority;

    public String getName() {
        return name;
    }


    public Set<String> getVars() {
        return vars;
    }

    public Node(String name, List<Node> children) {
        this.name = name;
        this.children = children;
        updateVars();
        priority = 2;
        isBinOperator = false;
    }

    public Node(Node toCopy) {
        this.name = toCopy.name;
        this.children = new ArrayList<>();
        toCopy.children.forEach(node -> this.children.add(node.copy()));
        this.vars = new HashSet<>(toCopy.vars);
        this.isBinOperator = toCopy.isBinOperator;
        this.priority = toCopy.priority;
    }

    public Node apply(Map<String, Node> applyMap, boolean... proofNeeded) {
        if (proofNeeded.length != 0 && proofNeeded[0]) {
            Node cur = this;
            // in most cases generalized formula is already proven
            boolean proveGen = proofNeeded.length > 1 && proofNeeded[1];

            cur = PredicateCalculus.generalize(cur, applyMap.keySet(), proveGen);

            while (cur instanceof Quantified) {
                Var var = new Var(((Quantified) cur).getVariable());
                if (applyMap.containsKey(var.name)) {
                    Impl impl = new Impl(cur, cur.children.get(0).subst(var, applyMap.get(var.name)));
                    cur = PredicateCalculus.MP(impl);
                }
            }
            return cur;
        }

        Node res;
        if (this instanceof Var) {
            res = applyMap.containsKey(name) ? applyMap.get(name) : copy();
        } else {
            List<Node> childResults = new ArrayList<>();
            for (Node child : children) {
                boolean found = false;
                for (String var : applyMap.keySet())
                    if (child.vars.contains(var)) {
                        found = true;
                        break;
                    }
                if (found)
                    childResults.add(child.apply(applyMap));
                else childResults.add(child);
            }
            if (this instanceof Inc)
                res = new Inc(childResults.get(0));
            else {
                Node copy = copy();
                copy.children = childResults;
                copy.updateVars();
                res = copy;
            }
        }

        return res;
    }

    protected void updateVars() {
        vars = new HashSet<>();
        if (children != null) {
            for (Node child : children) {
                if (child == null) {
                    System.err.println("we have a problem");
                    return;
                }
                if (child.vars != null)
                    vars.addAll(child.vars);
            }
        }
    }

    public Node subst(Var var, Node theta) {
        if (this instanceof Var) return equals(var) ? theta : copy();
        else {
            if (this instanceof Quantified) {
                Quantified q = (Quantified) this;
                // attempt to substitute bound variable
                if (q.getVariable().equals(var.getName()))
                    return copy();
                else if ((theta)
                        .vars
                        .contains(q
                                .getVariable()))
                    throw new IllegalArgumentException("term " +
                            theta + " is not free to substitute variable " + var + " in formula " + this);
            }
            Node that = copy();
            for (int i = 0; i < children.size(); i++)
                that.children.set(i, children.get(i).subst(var, theta));
            that.updateVars();
            return that;
        }
    }

    @Override
    public String toString() {
        if (children == null || children.isEmpty())
            return name;
        else {
            if (isBinOperator)
                return children.get(0) + name + children.get(1);
            StringJoiner joiner = new StringJoiner(",", "(", ")");
            for (Node child : children) {
                joiner.add(child.toString());
            }
            return name + joiner;

        }

    }

    protected Node copy() {
        return new Node(this);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || !(o instanceof Node)) return false;

        Node node = (Node) o;

        if (isBinOperator != node.isBinOperator) return false;
        if (name != null ? !name.equals(node.name) : node.name != null) return false;
        if (children != null ? !children.equals(node.children) : node.children != null) return false;
        return vars != null ? vars.equals(node.vars) : node.vars == null;

    }

    @Override
    public int hashCode() {
        int result = (isBinOperator ? 1 : 0);
        result = 31 * result + (name != null ? name.hashCode() : 0);
        result = 31 * result + (children != null ? children.hashCode() : 0);
        result = 31 * result + (vars != null ? vars.hashCode() : 0);
        return result;
    }

    public static void test() {
        Eq e = new Eq(new Var("a"), new Var("b"));
        Node e1 = e.copy();
        e1.children = null;
        System.out.println("null or not: " + (e.children == null));
    }


    public void prove() {
        PredicateCalculus.generalize(this, true);
    }

    /**
     * could be applied to a set of variables of an axiom or a lemma
     */
    public Node rename(Map<String, Node> usageMap) {
        Set<String> usageVars = new HashSet<>();
        boolean foundEqualVars = false;
        for (Node n : usageMap.values()) {
            usageVars.addAll(n.getVars());
            for (String v : n.getVars())
                if (vars.contains(v)) {
                    foundEqualVars = true;
                    break;
                }
        }
        if (!foundEqualVars)
            return apply(usageMap, true);
        int max = 0;
        for (String s : usageVars)
            max = Math.max(max, s.length());
        for (String var : vars) {
            max = Math.max(max, var.length());
        }
        Node res = copy();
        Map<String, Node> renameMap = new HashMap<>();
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < max + vars.size(); ++i)
            sb.append('0');
        // make fresh vars, i.e. not used neither in lemma nor in its application
        int j = 0;
        Map<String, Node> reverseMap = new HashMap<>();

        for (String var : vars) {
            String substring = sb.toString().substring(0, max - var.length() + j + 1);
            renameMap.put(var, new Var("x" + substring));
            reverseMap.put("x" + substring, new Var(var));
//            res = res.subst(new Var(var), new Var("x" + sb.toString().substring(0, max + j + 1)));
            ++j;
        }
//        System.out.println("rename to fresh vars");
        res = res.apply(renameMap, true);
//        System.out.println("generalize using fresh vars");
        PredicateCalculus.generalize(res, true);
        Map<String, Node> appMap = new HashMap<>();
        for (Map.Entry<String, Node> pair : reverseMap.entrySet()) {
            Node value = usageMap.get(pair.getValue().toString());
            if (value != null)
                appMap.put(pair.getKey(), value);
        }
//        System.out.println("use generalized lemma with fresh vars");
        res = res.apply(appMap, true);
        return res;
    }

}
