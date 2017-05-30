package proofs;

import com.google.common.collect.HashMultimap;
import com.google.common.collect.Multimap;
import node.*;
import parsing.Parser;

import java.io.BufferedWriter;
import java.io.IOException;
import java.util.*;
import java.util.stream.Collectors;

/**
 * @author Roman Golchin (romagolchin@gmail.com)
 */
public class Checker {

    static final String ERR_WRONG_FROM = "Вывод некорректен начиная с формулы номер %d";
    static final String ERR_TERM = "терм %s не свободен для подстановки в формулу %s вместо переменной %s";
    static final String ERR_FREE_VAR = "переменная %s входит свободно в формулу %s";
    static final String ERR_FV_ASSUMPTION =
            "используется правило с квантором по переменной %s, входящей свободно в допущение %s";

    static final String ERR_NO_PROOF = "Не доказано";

    static final String ANN_SCHEME = "Сх. акс. ";
    static final String ANN_HYPO = "Предп. ";
    static final String ANN_MP = "M.P. ";

    Parser parser;

    boolean strict;
    boolean deduction;
    boolean annotation;

    Multimap<Node, Integer> rightPartToInds;
    HashMap<Node, Integer> leftPartToMinInd;
    HashSet<Node> proven;

    List<Node> curNodes;
    List<AnnotatedNode> annotatedNodes = new ArrayList<>();
    BufferedWriter writer;

    public Checker(Parser parser, BufferedWriter writer, boolean strict, boolean deduction, boolean annotation) {
        this.parser = parser;
        curNodes = new ArrayList<>();
        rightPartToInds = HashMultimap.create();
        leftPartToMinInd = new HashMap<>();
        proven = new HashSet<>();
        this.strict = strict;
        this.writer = writer;
        this.deduction = deduction;
        this.annotation = annotation;
    }


    private void writeln(Object o) throws IOException {
        writer.write(String.valueOf(o) + "\n");
    }

    public void checkAll() throws IOException {
        for (; ; ) {
            try {
                Node formula = parser.nextExpr();
                if (formula == null)
                    continue;
                ProofType type = null;
                String error = "";
                try {
                    type = check(formula);
                } catch (ProofException e) {
                    error = e.getMessage();
                }
                if (type != null) {
                    if (formula instanceof Impl) {
                        Impl impl = (Impl) formula;
                        rightPartToInds.put(impl.getRight(), curNodes.size());
                    }
                    leftPartToMinInd.putIfAbsent(formula, curNodes.size());
                    proven.add(formula);
//                    if (formula.equals(parser.nextExpr("P(f(a),g(b))->?b1(P(f(a),g(b1)))")))
//                        System.out.println(formula);
//                    if (type instanceof ProofType.Forall || type instanceof ProofType.Exists)
//                        System.out.println(formula);
                    if (deduction)
                        annotatedNodes.add(new AnnotatedNode(formula, type));
                } else {
                    if (strict) {
                        String message = String.format(ERR_WRONG_FROM, parser.getLine() - 1);
                        writeln(error.isEmpty() ? message : message + ": " + error);
                        return;
                    }
                }
                if (annotation)
                    writeln(String.format("(%d) %s (%s)", parser.getLine() - 1, String.valueOf(formula),
                            type == null ? ERR_NO_PROOF : String.valueOf(type)));
                curNodes.add(formula);
            } catch (IOException e) {
                break;
            }
        }
        if (deduction) {
            System.out.println("deducing");
            List<Node> assumptions = parser.getAssumptions();
            Node node = curNodes.isEmpty() ? parser.getProposition() : curNodes.get(curNodes.size() - 1);
            System.err.println(node);
            if (assumptions.isEmpty()) {
                writeln("|-" + node);
            } else writeln(assumptions.subList(0, assumptions.size() - 1).stream().map(Node::toString).collect(
                    Collectors.joining(", ", "", "|-"))
                    + new Impl(assumptions.get(assumptions.size() - 1),
                    node));
            int cnt = 1;
            for (int k = 0; k < annotatedNodes.size(); ++k) {
                AnnotatedNode a = annotatedNodes.get(k);
                System.err.println("type " + a.type);
                String str = a.node.toString() + "\n";
                if (!assumptions.isEmpty()) {
                    List<Node> deduction = Deductions.deduction(assumptions.get(assumptions.size() - 1), a);
                    System.err.println((k + 1) + " " + cnt + " " + (cnt + deduction.size() - 1));
                    cnt += deduction.size();
                    str = Deductions.lineBreakJoin(deduction);
                }
                writer.write(str);
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
                    Node operand = quantified.getOperand().copy();
                    operand.getFreeVars();
                    getSubst(quantified.getVariable(), operand, impl.getRight());
                    return true;
                } catch (ProofException e) {
//                    e.printStackTrace();
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
                    Node operand = quantified.getOperand().copy();
                    operand.getFreeVars();
                    getSubst(quantified.getVariable(), operand, impl.getLeft());
                    return true;
                } catch (ProofException e) {
                    e.printStackTrace();
                    return false;
                }
            }
        }
        return false;
    }


    private static Node getSubst(String var, Node node, Node substNode) {
        return getSubst(node, var, node, substNode);
    }

    /**
     * @param formula   the whole formula should be stored to output correct errors
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
                System.err.println(("substNode " + substNode.getName() + " node " + node));
                throw new ProofException(ERR_NO_PROOF);
            }
            return new Var(var);
        } else {
            if (node instanceof Inc && substNode instanceof Inc) {
                Inc incNode = (Inc) node;
                Inc incSubstNode = (Inc) substNode;
                int incNodeNumber = incNode.getNumber();
                int incSubstNodeNumber = incSubstNode.getNumber();
                if (incNodeNumber == incSubstNodeNumber)
                    return getSubst(formula, var, incNode.getOperand(), incSubstNode.getOperand());
                if (incNodeNumber < incSubstNodeNumber)
                    return getSubst(formula, var, incNode.getOperand(),
                            new Inc(incSubstNode.getOperand(), incSubstNodeNumber - incNodeNumber));
                else
                    return getSubst(formula, var, new Inc(incNode.getOperand(), incNodeNumber - incSubstNodeNumber),
                            incSubstNode.getOperand());
            }
            if (node.getChildren().size() == substNode.getChildren().size()) {
                Node subst = variable;
                for (int i = 0; i < node.getChildren().size(); i++) {
                    Node curSubst = getSubst(formula, var, node.getChildren().get(i), substNode.getChildren().get(i));
                    if (subst.equals(variable)) {
                        subst = curSubst;
                    } else if (!curSubst.equals(variable) && !subst.equals(curSubst))
                        throw new ProofException(ERR_NO_PROOF, "different substitutions " + curSubst + " " + subst);

                }
                return subst;
            }
        }

        throw new ProofException("different structure " + node + " " + var + " " + substNode);
    }

    private ProofType check(Node formula) {
        // check for arithmetic axiom
        for (int i = 0; i < Arithmetic.AXIOMS.length; i++) {
            if (formula.match(Arithmetic.AXIOMS[i], true))
                return new ProofType.Scheme(-i);
        }
        if (formula instanceof Impl) {
            // check for axiom scheme
            for (int i = 0; i < PCalculus.SCHEMES.length; i++) {
                if (formula.match(PCalculus.SCHEMES[i], false))
                    return new ProofType.Scheme(i);
            }
            // check for induction
            Node psy = ((Impl) formula).getRight();
            Node antecedent = ((Impl) formula).getLeft();
            if (antecedent instanceof And) {
                Node base = ((And) antecedent).getLeft();
                if (((And) antecedent).getRight() instanceof Quantified) {
                    Quantified step = (Quantified) ((And) antecedent).getRight().copy();
                    step.getFreeVars();
                    String x = step.getVariable();
                    if (step.getOperand() instanceof Impl) {
                        Impl impl = (Impl) step.getOperand();
                        if (psy.getFreeVars().contains(x)) {
                            Var var = new Var(x);
                            if (impl.getLeft().equals(psy) && psy.subst(var, new Inc(var)).equals(impl.getRight())
                                    && psy.subst(var, new Node(Arithmetic.ZERO, new ArrayList<>())).equals(base))
                                return new ProofType.Scheme(-Arithmetic.AXIOMS.length);
                        }
                    }
                }
            }
            if (checkForallScheme(formula))
                return new ProofType.Scheme(10);
            else if (checkExistsScheme(formula))
                return new ProofType.Scheme(11);
            else {
                // check for predicate calculus rules
                Node left = ((Impl) formula).getLeft();
                Node right = ((Impl) formula).getRight();
                if (right instanceof Quantified) {
                    Quantified quantified = (Quantified) right;
                    if (quantified.getName().equals(PCalculus.FORALL) &&
                            proven.contains(new Impl(left, quantified.getOperand()))) {
                        String variable = quantified.getVariable();
                        if (left.getFreeVars().contains(variable))
                            throw new ProofException(String.format(ERR_FREE_VAR, variable, left.toString()));
                        if (deduction)
                            checkVarInAssumptions(variable);
                        return new ProofType.Forall();
                    }
                }
                if (left instanceof Quantified) {
                    if (curNodes.size() == 2041)
                        System.out.println();
                    Quantified quantified = (Quantified) left;
                    if (quantified.getName().equals(PCalculus.EXISTS) &&
                            proven.contains(new Impl(quantified.getOperand(), right))) {
                        String variable = quantified.getVariable();
                        if (right.getFreeVars().contains(variable))
                            throw new ProofException(String.format(ERR_FREE_VAR, variable, right.toString()));
                        if (deduction)
                            checkVarInAssumptions(variable);
                        return new ProofType.Exists();
                    }

                }
            }
        }
        // check for assumption
//        System.out.println(parser.getAssumptions().size());
        for (int i = 0; i < parser.getAssumptions().size(); i++) {
            Node a = parser.getAssumptions().get(i);
            if (a.equals(formula))
                return new ProofType.Assumption(i);
        }
        // check for MP
        for (int i = 0; i < curNodes.size(); i++) {
            // maximal index of an expression of the form: a -> node
            for (int secondInd : Util.nullCheck(rightPartToInds.get(formula))) {
                Integer firstInd = null;
                try {
                    firstInd = leftPartToMinInd.get(((Impl) curNodes.get(secondInd)).getLeft());
                } catch (ClassCastException e) {
                    System.err.println(formula);
                    System.err.println(parser.getLine());
                }
                if (firstInd != null) {
                    return new ProofType.MP(curNodes.get(firstInd), firstInd, secondInd);
                }
            }
        }
        return null;
    }

    private void checkVarInAssumptions(String variable) {
        List<Node> assumptions = parser.getAssumptions();
        Node a = assumptions.get(assumptions.size() - 1);
        if (a.getFreeVars().contains(variable))
            throw new ProofException(String.format(ERR_FV_ASSUMPTION, variable, a.toString()));
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
        Parser parser = new Parser();
//        Node bad = parser.nextExpr("!b'=0");
//        Node worse = parser.nextExpr("0+0=0");
        System.out.println(parser.nextExpr("!@b?bP(f(a),g(b))->@b?bP(f(a),g(b))|!@b?bP(f(a),g(b))")
                .match(PCalculus.SCHEMES[6], false));
        Node worst = parser.nextExpr("P(f(a),g(b))->?b1(P(f(a),g(b1)))");
        System.out.println(checkExistsScheme(worst));
//        System.out.println(worst == null);
        System.out.println(worst.getFreeVars());
//        System.out.println(bad.match(Arithmetic.AXIOMS[3], true));
//        System.out.println(worse.match(Arithmetic.AXIOMS[5], true));
        Impl impl = (Impl) parser.nextExpr("@b(@a(a=b'''->a'=b))->@a(a=(0)'''''->a'=(0)'')");
//        Impl impl = (Impl) parser.nextExpr("@x(x=(a+b)'->(a+b)'=x)->a+b'=(a+b)'->(a+b)'=a+b'");
        Node node = impl.getLeft().getChildren().get(0);
        System.out.println("node " + node);
        System.out.println("substNode " + impl.getRight());
        try {
            System.out.println(Checker.getSubst(((Quantified) impl.getLeft()).getVariable(), node, impl.getRight()));
        } catch (ProofException e) {
            e.printStackTrace();
            e.printExtraMessage();
        }
        System.out.println(new Or(new Var("A"), new Or(new Var("B"), new Var("C"))));
//        try (BufferedReader reader = new BufferedReader(new FileReader("test-checker"))) {
//            Parser parser = new Parser(reader, false);
//            Checker checker = new Checker(parser);
//            System.out.println(new Quantified(PCalculus.FORALL, "x", new Eq(new Var("x"),
//                    new Node("0", new ArrayList<>()))).getFreeVars());
//            for (; ; ) {
//                String var = "x";
//                try {
//                    Node node = parser.nextExpr();
//                    Node substNode = parser.nextExpr();
//                    if (node != null && substNode != null) {
//                        System.out.println("free in substNode " + substNode.getFreeVars());
//                        writeln("free in node " + node.getFreeVars());
//                        writeln("vars of node " + node.getVars());
//                        System.out.println("Subst = " + Checker.getSubst(node, var, node, substNode));
//                    Impl exists = new Impl(substNode, new Quantified(PCalculus.EXISTS, var, node));
//                    Impl forall = new Impl(new Quantified(PCalculus.FORALL, var, node), substNode);
//                    System.out.println(Checker.checkExistsScheme(exists));
//                    System.out.println(Checker.checkExistsScheme(forall));
//                    System.out.println(Checker.checkForallScheme(forall));
//                    System.out.println(Checker.checkForallScheme(exists));
//                    }
//                } catch (IndexOutOfBoundsException e) {
//                    break;
//                } catch (ProofException pe) {
//                    pe.printStackTrace();
//                }
//            }

//        } catch (IOException ignored) {
//        }
    }
}
