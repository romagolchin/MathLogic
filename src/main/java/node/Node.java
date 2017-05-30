package node;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import com.sun.istack.internal.Nullable;
import org.jetbrains.annotations.NotNull;
import proofs.Arithmetic;
import proofs.PCalculus;

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
    protected Set<String> freeVars;
    protected int priority;

    public Set<String> getFreeVars() {
        return freeVarsHelper(new HashSet<>(), this);
    }

    public List<Node> getChildren() {
        return children;
    }

    public String getName() {
        return name;
    }


    public Set<String> getVars() {
        return vars;
    }

    private static Set<String> freeVarsHelper(Set<String> curBoundVars, Node node) {
        HashSet<String> res = new HashSet<>();
        String bound = null;
        if (node.freeVars != null) {
            return node.freeVars;
        }
        if (node instanceof Var) {
            if (!curBoundVars.contains(node.name)) {
                return node.freeVars = new HashSet<>(Collections.singleton(node.name));
            }
        } else {
            if (node instanceof Quantified) {
                bound = ((Quantified) node).getVariable();
                curBoundVars.add(bound);
            }
            for (Node child : node.children) {
                res.addAll(freeVarsHelper(curBoundVars, child));
            }
        }
        curBoundVars.remove(bound);
        return node.freeVars = res;
    }

    public Node(String name, @NotNull List<Node> children) {
        freeVars = null;
        this.name = name;
        this.children = children;
        updateVars();
        priority = 10;
        isBinOperator = false;
    }

    protected Node(Node toCopy) {
        this.name = toCopy.getName();
        this.children = new ArrayList<>();
        toCopy.getChildren().forEach(node -> this.children.add(node.copy()));
        this.vars = new HashSet<>(toCopy.vars);
        this.freeVars = null;
        this.isBinOperator = toCopy.isBinOperator;
        this.priority = toCopy.priority;
    }

    public Node apply(Map<String, Node> applyMap, boolean... proofNeeded) {
        if (proofNeeded.length != 0 && proofNeeded[0]) {
            Node cur = this;
            // in most cases generalized formula is already proven
            boolean proveGen = proofNeeded.length > 1 && proofNeeded[1];

            cur = PCalculus.generalize(cur, applyMap.keySet(), proveGen);

            while (cur instanceof Quantified) {
                Var var = new Var(((Quantified) cur).getVariable());
                if (applyMap.containsKey(var.getName())) {
                    Impl impl = new Impl(cur, cur.getChildren().get(0).subst(var, applyMap.get(var.getName())));
                    cur = PCalculus.MP(impl);
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
                    return;
                }
                if (child.vars != null)
                    vars.addAll(child.vars);
            }
        }
    }

    public Node subst(Var var, Node theta) {
        if (this instanceof Var)
            return equals(var) ? theta : copy();
        else {
            if (this instanceof Inc && children.get(0).equals(var))
                return new Inc(theta, ((Inc) this).number);
            if (this instanceof Quantified) {
                Quantified q = (Quantified) this;
                // attempt to substitute bound variable
                if (q.getVariable().equals(var.getName()))
                    return copy();
                else if (theta.vars
                        .contains(q.getVariable()))
                    throw new IllegalArgumentException("term " +
                            theta + " is not free to substitute variable " + var + " in formula " + this);
            }
            Node that = copy();
            for (int i = 0; i < children.size(); i++)
                that.getChildren().set(i, children.get(i).subst(var, theta));
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

    public Node copy() {
        return new Node(this);
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || !(o instanceof Node)) return false;

        Node node = (Node) o;
        if (node instanceof Inc && ((Inc) node).number == 0)
            node = ((Inc) o).getOperand();
        Node that = this;
//        if (this instanceof Inc && ((Inc) this).number == 0)
//            that = ((Inc) this).getOperand();

        if (that.isBinOperator != node.isBinOperator) return false;
        if (that.name != null ? !that.name.equals(node.getName()) : node.getName() != null) return false;
        if (that.children != null ? !that.children.equals(node.getChildren()) : node.getChildren() != null) return false;
        return that.vars != null ? that.vars.equals(node.vars) : node.vars == null;

    }

    @Override
    public int hashCode() {
        int result = (isBinOperator ? 1 : 0);
        result = 31 * result + (name != null ? name.hashCode() : 0);
        result = 31 * result + (children != null ? children.hashCode() : 0);
        result = 31 * result + (vars != null ? vars.hashCode() : 0);
        return result;
    }

    public void prove() {
        PCalculus.generalize(this, true);
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
            ++j;
        }
//        System.out.println("rename to fresh vars");
        res = res.apply(renameMap, true);
//        System.out.println("generalize using fresh vars");
        PCalculus.generalize(res, true);
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

    public boolean match(Node scheme, boolean isPlainAxiom) {
        Multimap<String, Node> res;
        try {
            res = matchHelper(this, scheme, isPlainAxiom);
            for (String s : res.keySet()) {
                if (res.get(s).size() != 1)
                    return false;
            }
            return true;
        } catch (IllegalArgumentException e) {
            return false;
        }
    }

    private static Multimap<String, Node> matchHelper(Node node, Node scheme, boolean isPlainAxiom) {

        Multimap<String, Node> res = HashMultimap.create();
        if (scheme.getChildren().isEmpty()) {
            if (scheme instanceof Var && !scheme.equals(Arithmetic.Z)) {
                if (isPlainAxiom && !(node instanceof Var))
                    throw new IllegalArgumentException(
                            node + " corresponds to var " + scheme + " but is not a var itself");
                Var var = (Var) scheme;
                res.put(var.getName(), node);
            } else if (!scheme.equals(node))
                throw new IllegalArgumentException();
            return res;
        }
        if (node.getChildren().size() == scheme.getChildren().size()) {
            if (!node.name.equals(scheme.name))
                throw new IllegalArgumentException(node + " and " + scheme + "have different names");
            for (int i = 0; i < node.getChildren().size(); i++) {
                res.putAll(matchHelper(node.getChildren().get(i), scheme.getChildren().get(i), isPlainAxiom));
            }
            return res;
        }
        throw new IllegalArgumentException(node + " and " + scheme + " have different structure");
    }

}
