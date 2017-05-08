package proofs;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import node.*;
import parsing.Parser;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.*;

/**
 * @author Roman Golchin (romagolchin@gmail.com)
 */
public class Checker {

    static final String ERR_WRONG_FROM = "Вывод некорректен начиная с формулы номер %s";
    static final String ERR_TERM = "терм %s не свободен для подстановки в формулу %s вместо переменной %s";
    static final String ERR_FREE_VAR = "переменная %s входит свободно в формулу %s";
    static final String ERR_FV_ASSUMPTION =
            "используется правило с квантором по переменной %s, входящей свободно в допущение %s";

    static final String ERR_NO_PROOF = "Не доказано";

    Parser parser;

    boolean strict;

    Multimap<Node, Integer> rightPartToInds;
    HashMap<Node, Integer> leftPartToMinInd;
    HashSet<Node> proven;

    List<Node> curNodes;

    public Checker(Parser parser) {
        this.parser = parser;
        curNodes = new ArrayList<>();
        rightPartToInds = HashMultimap.create();
        leftPartToMinInd = new HashMap<>();
    }


    public void checkAll() {
        for (; ; ) {
            try {
                Node formula = parser.nextExpr();
                ProofType type = check(formula);
                if (type != null) {
                    if (formula instanceof Impl) {
                        Impl impl = (Impl) formula;
                        rightPartToInds.put(impl.getRight(), parser.getLine() - 1);
                        leftPartToMinInd.putIfAbsent(formula, parser.getLine() - 1);
                    }
                    proven.add(formula);
                } else {
                    if (strict)
                        throw new ProofException(ERR_WRONG_FROM + parser.getLine());
                    else
                        System.err.println(ERR_NO_PROOF);
                }
            } catch (IOException | IndexOutOfBoundsException e) {
                break;
            } catch (ProofException pe) {
                System.err.println(pe.getMessage());
            }
        }
    }

    private static boolean checkForallScheme(Node node) {
        if (node instanceof Impl) {
            Impl impl = (Impl) node;
            Node left = impl.getLeft();
            if (left instanceof Quantified && left.getName().equals(PCalculus.FORALL)) {
                Quantified quantified = (Quantified) left;
                try {
                    getSubst(node, quantified.getVariable(), quantified.getOperand(), impl.getRight());
                    return true;
                } catch (ProofException e) {
                    e.printStackTrace();
                    return false;
                }
            }
        }
        return false;
    }

    private static boolean checkExistsScheme(Node node) {
        if (node instanceof Impl) {
            Impl impl = (Impl) node;
            Node right = impl.getRight();
            if (right instanceof Quantified && right.getName().equals(PCalculus.EXISTS)) {
                Quantified quantified = (Quantified) right;
                try {
                    getSubst(node, quantified.getVariable(), quantified.getOperand(), impl.getLeft());
                    return true;
                } catch (ProofException e) {
                    e.printStackTrace();
                    return false;
                }
            }
        }
        return false;
    }


    /**
     * @param var
     * @param node
     * @param substNode
     * @return a substitution of var (if such exists) that turns node to substNode
     */
    private static Node getSubst(Node formula, String var, Node node, Node substNode) {
        Var variable = new Var(var);
        if (node instanceof Var) {
            if (node.getName().equals(var)) {
                if (node.getFreeVars().contains(var)) {
                    for (String v : substNode.getVars())
                        if (!substNode.getFreeVars().contains(v))
                            throw new ProofException(
                                    String.format(ERR_TERM, substNode.toString(), formula.toString(), var));
                    return substNode;
                }
                if (substNode instanceof Var && substNode.getName().equals(var))
                    return substNode;
                System.err.println("substNode " + substNode.getName());
                throw new ProofException(ERR_NO_PROOF);
            }
            return new Var(var);
        } else {
            if (node.getChildren().size() == substNode.getChildren().size()) {
                Node subst = variable;
                for (int i = 0; i < node.getChildren().size(); i++) {
                    Node curSubst = getSubst(formula, var, node.getChildren().get(i), substNode.getChildren().get(i));
                    if (subst.equals(variable)) {
                        subst = curSubst;
                    } else if (!curSubst.equals(variable) && !subst.equals(curSubst))
                        throw new ProofException(ERR_NO_PROOF);

                }
                return subst;
            }
        }

        throw new ProofException("different structure");
    }

    private ProofType check(Node formula) {
        if (formula instanceof Impl) {
            // check for axiom scheme
            for (int i = 0; i < PCalculus.SCHEMES.length; i++) {
                if (formula.match(PCalculus.SCHEMES[i]))
                    return new ProofType.Scheme(i);
            }
            if (checkForallScheme(formula))
                return new ProofType.Scheme(10);
            else if (checkExistsScheme(formula))
                return new ProofType.Scheme(11);
                // check for predicate calculus rules
            else {
                Node left = ((Impl) formula).getLeft();
                Node right = ((Impl) formula).getRight();
                if (right instanceof Quantified) {
                    Quantified quantified = (Quantified) right;
                    if (quantified.getName().equals(PCalculus.FORALL) &&
                            proven.contains(new Impl(left, quantified.getOperand()))) {
                        String variable = quantified.getVariable();
                        if (left.getFreeVars().contains(variable))
                            throw new ProofException(String.format(ERR_FREE_VAR, variable, left.toString()));
                        return new ProofType.Forall();
                    }
                }
                if (left instanceof Quantified) {
                    Quantified quantified = (Quantified) left;
                    if (quantified.getName().equals(PCalculus.EXISTS) &&
                            proven.contains(new Impl(quantified.getOperand(), right))) {
                        String variable = quantified.getVariable();
                        if (right.getFreeVars().contains(variable))
                            throw new ProofException(String.format(ERR_FREE_VAR, variable, right.toString()));
                        return new ProofType.Exists();
                    }

                }
            }
        }
        // check for assumption
        for (int i = 0; i < parser.getAssumptions().size(); i++) {
            Node a = parser.getAssumptions().get(i);
            if (a.equals(formula))
                return new ProofType.Assumption(i);
        }
        // check for MP
        for (int i = 0; i < curNodes.size(); i++) {
            // maximal index of an expression of the form: a -> node
            for (int secondInd : rightPartToInds.get(formula)) {
                Integer firstInd = leftPartToMinInd.get(curNodes.get(secondInd));
                if (firstInd != null)
                    return new ProofType.MP(firstInd, secondInd);
            }
        }
        return null;
    }

    public abstract static class ProofType {
        static final class MP extends ProofType {
            public MP(int first, int second) {
                this.first = first;
                this.second = second;
            }

            int first, second;
        }

        static final class Assumption extends ProofType {
            public Assumption(int n) {
                this.i = i;
            }

            int i;
        }

        static final class Scheme extends ProofType {
            public Scheme(int n) {
                this.i = i;
            }

            int i;
        }

        static final class Forall extends ProofType {
        }

        static final class Exists extends ProofType {
        }
    }

    static class ProofException extends RuntimeException {
        String extraMessage;

        public ProofException(String message) {
            super(message);
        }

        public ProofException(String message, String extraMessage) {
            super(message);
            this.extraMessage = extraMessage;
        }

        public void printExtraMessage() {
            System.err.println(extraMessage);
        }

    }

    public static void main(String[] args) {
        try (BufferedReader reader = new BufferedReader(new FileReader("test-checker"))) {
            Parser parser = new Parser(reader, false);
//            Checker checker = new Checker(parser);
//            System.out.println(new Quantified(PCalculus.FORALL, "x", new Eq(new Var("x"),
//                    new Node("0", new ArrayList<>()))).getFreeVars());
            for (; ; ) {
                String var = "x";
                try {
                    Node node = parser.nextExpr();
                    Node substNode = parser.nextExpr();
                    if (node != null && substNode != null) {
                        System.out.println("free in substNode " + substNode.getFreeVars());
                        System.err.println("free in node " + node.getFreeVars());
//                        System.err.println("vars of node " + node.getVars());
                        System.out.println("Subst = " + Checker.getSubst(node, var, node, substNode));
//                    Impl exists = new Impl(substNode, new Quantified(PCalculus.EXISTS, var, node));
//                    Impl forall = new Impl(new Quantified(PCalculus.FORALL, var, node), substNode);
//                    System.out.println(Checker.checkExistsScheme(exists));
//                    System.out.println(Checker.checkExistsScheme(forall));
//                    System.out.println(Checker.checkForallScheme(forall));
//                    System.out.println(Checker.checkForallScheme(exists));
                    }
                } catch (IndexOutOfBoundsException e) {
                    break;
                } catch (ProofException pe) {
                    pe.printStackTrace();
                }
            }

        } catch (IOException ignored) {
        }
    }
}
