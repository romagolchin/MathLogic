package parsing;

import node.*;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;
import proofs.Arithmetic;

import java.io.BufferedReader;
import java.io.FileReader;
import java.io.IOException;
import java.util.*;

/**
 * Created by Roman on 02/04/2017.
 */
public class Parser {
    int line;
    Node proposition;
    List<Node> assumptions = new ArrayList<>();
    private BufferedReader reader;
    private Token[] tokensByPriority = {Token.OR, Token.AND, Token.ADD, Token.MUL};

    Node lastTerm;

    Lexer lexer;

    public Node getProposition() {
        return proposition;
    }

    public List<Node> getAssumptions() {
        return assumptions;
    }

    public int getLine() {
        return line;
    }

    public Parser() {
    }

    public Parser(BufferedReader reader) throws IOException {
        this(reader, true);
    }

    public Parser(BufferedReader reader, boolean header) throws IOException {
        this.reader = reader;
        line = 0;
        if (header)
            header();
    }

    private boolean accept(Token token) {
        if (lexer.token == token) {
            lexer.next();
            return true;
        } else return false;
    }

    private void forceAccept(Token token) {
        if (lexer.token != token)
            throw new ParseException(Lexer.charMap.get(token));
        lexer.next();
    }

    @Nullable private List<Node> getArgs() {
        List<Node> args = null;
        if (accept(Token.OPEN)) {
            args = new ArrayList<>();
            do {
                lexer.next();
                args.add(leftAssociative(2));
            } while (lexer.token == Token.COMMA);
            forceAccept(Token.CLOSE);
        }
        return args;
    }

    private Node multiplicand() {
        Node node = null;
        if (lexer.token == Token.VAR) {
            String var = lexer.var;
            lexer.next();
            List<Node> args = getArgs();
            node = args == null ? new Var(var) : new Node(var, args);
        } else if (accept(Token.ZERO)) {
            node = new Node(Arithmetic.ZERO, new ArrayList<>());
        } else {
            if (accept(Token.OPEN)) {
                node = leftAssociative(2);
                forceAccept(Token.CLOSE);
            }
        }
        return putIncs(node);
    }

    private Node putIncs(Node mul) {
        int inc = 0;
        while (accept(Token.INC))
            inc++;
        return Inc.create(mul, inc);
    }

    private Node leftAssociative(int priority) {
        if (priority > 3)
            return multiplicand();
        return leftAssociative(priority == 1 ? unary() : leftAssociative(priority + 1), priority);
    }


    private Node leftAssociative(Node acc, int priority) {
        if (priority > 3)
            return multiplicand();
        while (lexer.token == tokensByPriority[priority]) {
            lexer.next();
            Node operand = priority == 1 ? unary() : leftAssociative(priority + 1);
            acc = BinaryNode.newBinaryNode(String.valueOf(Lexer.charMap.get(tokensByPriority[priority])), acc, operand);
        }
        return acc;
    }

    private Node variable() {
        if (lexer.token == Token.VAR) {
            lexer.next();
            return new Var(lexer.var);
        }
        throw new IllegalArgumentException("expected variable at position " + lexer.pos + " on line " + line);
    }

    private Node predicate() {
        if (lexer.token == Token.PRED) {
            lexer.next();
            List<Node> args = getArgs();
            return new Node(lexer.pred, args == null ? new ArrayList<>() : args);
        } else {
            Node left = leftAssociative(2);
            if (!accept(Token.EQ)) {
                lastTerm = left;
                throw new IncompleteExprException();
            }
            return new Eq(left, leftAssociative(2));
        }
    }

    private Node unary() {
        int nots = 0;
        while (lexer.token == Token.NOT) {
            lexer.next();
            nots++;
        }
        Node node = null;
        boolean f = false;
        if (lexer.token == Token.OPEN) {
            lexer.next();
            try {
                node = implication();
                forceAccept(Token.CLOSE);
            } catch (IncompleteExprException e) {
                forceAccept(Token.CLOSE);
                lastTerm = leftAssociative(leftAssociative(putIncs(lastTerm), 3), 2);
                if (accept(Token.EQ))
                    return new Eq(lastTerm, leftAssociative(2));
                throw e;
            }

            f = true;
        }
        if (!f) {
            if (lexer.token == Token.FORALL || lexer.token == Token.EXISTS) {
                Token t = lexer.token;
                lexer.next();
                node = new Quantified(Lexer.charMap.get(t).toString(),
                        variable().getName(),
                        unary());
            } else
                node = predicate();
        }
        for (int i = 0; i < nots; ++i)
            node = new Not(node);
        return node;
    }

    private Node implication() {
        Node disj = leftAssociative(0);
        if (lexer.token == Token.IMPL) {
            lexer.next();
            return new Impl(disj, implication());
        } else return disj;
    }

    // either exception is thrown, or returned list contains at least 1 element (the proposition)
    private void header() throws IllegalArgumentException, IOException {
        lexer = new Lexer(reader.readLine());
        List<Node> header = new ArrayList<>();
        while (lexer.token != Token.PROV && lexer.token != Token.END) {
            header.add(implication());
            if (!accept(Token.COMMA))
                break;
        }
        try {
            forceAccept(Token.PROV);
            header.add(implication());
        } catch (Exception e) {
            throw new IllegalArgumentException("failed to parse header", e);
        }
        assumptions = header.subList(0, Math.max(0, header.size() - 1));
        proposition = header.get(header.size() - 1);
        line++;
    }

    @Nullable
    public Node nextExpr(@NotNull String expr) {
        Node implication = null;
        if (!expr.isEmpty()) {
            lexer = new Lexer(expr);
            lastTerm = null;
            implication = implication();
//            System.out.println(implication);
        }
        line++;
        return implication;
    }

    public Node nextExpr() throws IOException {
        String cur;
        Node implication;
        if ((cur = reader.readLine()) == null)
            throw new IOException("failed to get next expression");
        implication = nextExpr(cur);
        if (implication != null)
            implication.getFreeVars();
        return implication;
    }

    class ParseException extends RuntimeException {
        ParseException(char exp) {
            super("expected character " + exp + " at position " + lexer.pos + " on line " + line);
        }
    }

    class IncompleteExprException extends RuntimeException {
        public IncompleteExprException() {
        }
    }


    public static void main(String[] args) {
        try (BufferedReader reader = new BufferedReader(new FileReader("proof"))) {
            Parser parser = new Parser(reader);
            for (; ; ) {
                try {
                    parser.nextExpr();
                } catch (IndexOutOfBoundsException e) {
                    break;
                }
            }
        } catch (IOException ignored) {
        }
    }
}
