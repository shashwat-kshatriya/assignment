import java.io.*;
import java.math.BigInteger;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

public class Main {

    // ===== Exact rational (BigInteger) =====
    static final class Frac implements Comparable<Frac> {
        final BigInteger num; // numerator
        final BigInteger den; // denominator > 0

        Frac(BigInteger n, BigInteger d) {
            if (d.signum() == 0) throw new ArithmeticException("Denominator is zero");
            if (d.signum() < 0) { n = n.negate(); d = d.negate(); }
            BigInteger g = n.gcd(d);
            if (!g.equals(BigInteger.ONE)) { n = n.divide(g); d = d.divide(g); }
            this.num = n; this.den = d;
        }
        static Frac of(long v) { return new Frac(BigInteger.valueOf(v), BigInteger.ONE); }
        static Frac of(BigInteger v) { return new Frac(v, BigInteger.ONE); }
        Frac add(Frac o) { return new Frac(this.num.multiply(o.den).add(o.num.multiply(this.den)), this.den.multiply(o.den)); }
        Frac sub(Frac o) { return new Frac(this.num.multiply(o.den).subtract(o.num.multiply(this.den)), this.den.multiply(o.den)); }
        Frac mul(Frac o) { return new Frac(this.num.multiply(o.num), this.den.multiply(o.den)); }
        Frac div(Frac o) { return new Frac(this.num.multiply(o.den), this.den.multiply(o.num)); }
        boolean isInteger() { return den.equals(BigInteger.ONE); }
        boolean equalsInt(BigInteger v) { return isInteger() && num.equals(v); }
        public int compareTo(Frac o) { return this.num.multiply(o.den).compareTo(o.num.multiply(this.den)); }
        public String toString() { return isInteger() ? num.toString() : (num + "/" + den); }
    }

    static final class Point {
        final int x;
        final BigInteger y;
        Point(int x, BigInteger y) { this.x = x; this.y = y; }
        public String toString() { return "(" + x + "," + y + ")"; }
    }

    // ===== Lagrange evaluation at arbitrary x0 =====
    static Frac lagrangeAtX(List<Point> pts, Frac x0) {
        Frac sum = Frac.of(0);
        int k = pts.size();
        for (int i = 0; i < k; i++) {
            Point pi = pts.get(i);
            Frac term = Frac.of(pi.y);
            Frac Li = Frac.of(1);
            for (int j = 0; j < k; j++) if (i != j) {
                Point pj = pts.get(j);
                Li = Li.mul( x0.sub(Frac.of(pj.x)).div( Frac.of(pi.x - pj.x) ) );
            }
            sum = sum.add(term.mul(Li));
        }
        return sum;
    }

    // ===== Recover full coefficients (monomial basis) via Newton divided differences, then expand =====
    static List<Frac> interpolateCoefficients(List<Point> in) {
        List<Point> pts = new ArrayList<>(in);
        pts.sort(Comparator.comparingInt(p -> p.x));

        int k = pts.size();
        Frac[][] dd = new Frac[k][k];
        for (int i = 0; i < k; i++) dd[i][0] = Frac.of(pts.get(i).y);
        for (int j = 1; j < k; j++) {
            for (int i = 0; i < k - j; i++) {
                Frac num = dd[i+1][j-1].sub(dd[i][j-1]);
                Frac den = Frac.of(pts.get(i + j).x - pts.get(i).x);
                dd[i][j] = num.div(den);
            }
        }

        // Convert Newton form to monomial: start with 0
        List<Frac> coeff = new ArrayList<>();
        coeff.add(Frac.of(0)); // degree 0

        for (int j = 0; j < k; j++) {
            if (j == 0) {
                coeff.set(0, coeff.get(0).add(dd[0][0]));
                continue;
            }
            int xPrev = pts.get(j - 1).x;

            // multiply by (x - xPrev)
            List<Frac> next = new ArrayList<>(Collections.nCopies(coeff.size() + 1, Frac.of(0)));
            for (int d = 0; d < coeff.size(); d++) {
                // * x
                next.set(d + 1, next.get(d + 1).add(coeff.get(d)));
                // * (-xPrev)
                next.set(d, next.get(d).sub(coeff.get(d).mul(Frac.of(xPrev))));
            }
            coeff = next;

            // add dd[0][j] to constant term
            coeff.set(0, coeff.get(0).add(dd[0][j]));
        }

        // ensure length = k (degree m = k-1)
        while (coeff.size() < k) coeff.add(Frac.of(0));
        return coeff; // index = power of x: a0, a1, ..., a_m
    }

    static final class BestFit {
        List<Point> basis;
        int matches;
        Frac secret;          // f(0)
        List<Frac> coeffs;    // a0..a_m
    }

    static BestFit solve(List<Point> all, int k) {
        List<int[]> combs = combinations(all.size(), k);
        BestFit best = null;

        for (int[] idxs : combs) {
            List<Point> subset = new ArrayList<>(k);
            for (int i : idxs) subset.add(all.get(i));

            Frac secret = lagrangeAtX(subset, Frac.of(0));
            int hits = 0;
            for (Point p : all) {
                Frac val = lagrangeAtX(subset, Frac.of(p.x));
                if (val.equalsInt(p.y)) hits++;
            }

            if (best == null || hits > best.matches) {
                best = new BestFit();
                best.basis = subset;
                best.matches = hits;
                best.secret = secret;
            }
        }

        if (best != null) best.coeffs = interpolateCoefficients(best.basis);
        return best;
    }

    static List<int[]> combinations(int n, int k) {
        List<int[]> res = new ArrayList<>();
        int[] idx = new int[k];
        for (int i = 0; i < k; i++) idx[i] = i;
        while (true) {
            res.add(idx.clone());
            int p = k - 1;
            while (p >= 0 && idx[p] == n - k + p) p--;
            if (p < 0) break;
            idx[p]++;
            for (int i = p + 1; i < k; i++) idx[i] = idx[i - 1] + 1;
        }
        return res;
    }

    // ===== Minimal JSON parser (regex-based for the given format) =====
    static final Pattern KEYS_BLOCK =
            Pattern.compile("\"keys\"\\s*:\\s*\\{([^}]*)\\}", Pattern.DOTALL);
    static final Pattern NK_IN_KEYS =
            Pattern.compile("\"n\"\\s*:\\s*(\\d+)|\"k\"\\s*:\\s*(\\d+)");
    static final Pattern SHARE_ENTRY =
            Pattern.compile("\"(\\d+)\"\\s*:\\s*\\{\\s*\"base\"\\s*:\\s*\"(\\d+)\"\\s*,\\s*\"value\"\\s*:\\s*\"([0-9A-Za-z]+)\"\\s*\\}", Pattern.DOTALL);

    static final class ParsedInput {
        int n;
        int k;
        List<Point> points = new ArrayList<>();
    }

    static ParsedInput parseJson(String json) {
        ParsedInput out = new ParsedInput();

        // keys.n and keys.k
        Matcher keysM = KEYS_BLOCK.matcher(json);
        if (!keysM.find())
            throw new IllegalArgumentException("Missing 'keys' block");
        String keysBlock = keysM.group(1);
        Matcher nk = NK_IN_KEYS.matcher(keysBlock);
        boolean sawN = false, sawK = false;
        while (nk.find()) {
            String nStr = nk.group(1);
            String kStr = nk.group(2);
            if (nStr != null) { out.n = Integer.parseInt(nStr); sawN = true; }
            if (kStr != null) { out.k = Integer.parseInt(kStr); sawK = true; }
        }
        if (!sawN || !sawK) throw new IllegalArgumentException("Missing n or k in keys");

        // shares: any "number": { "base":"..", "value":".." }
        Matcher m = SHARE_ENTRY.matcher(json);
        while (m.find()) {
            int x = Integer.parseInt(m.group(1));
            int base = Integer.parseInt(m.group(2));
            String val = m.group(3).toLowerCase(Locale.ROOT);

            if (base < 2 || base > 36)
                throw new IllegalArgumentException("Unsupported base: " + base + " for x=" + x);

            BigInteger y = new BigInteger(val, base);
            out.points.add(new Point(x, y));
        }

        return out;
    }

    // ===== Pretty polynomial string =====
    static String polyToString(List<Frac> a) {
        StringBuilder sb = new StringBuilder();
        boolean any = false;
        for (int i = a.size() - 1; i >= 0; i--) {
            Frac c = a.get(i);
            if (c.num.equals(BigInteger.ZERO)) continue;
            if (any) sb.append(" + ");
            sb.append("(").append(c).append(")");
            if (i >= 1) sb.append("*x");
            if (i >= 2) sb.append("^").append(i);
            any = true;
        }
        return any ? sb.toString() : "0";
    }

    public static void main(String[] args) throws Exception {
        // Read full STDIN as JSON string
        BufferedReader br = new BufferedReader(new InputStreamReader(System.in));
        StringBuilder sb = new StringBuilder();
        for (String line; (line = br.readLine()) != null;) sb.append(line).append('\n');
        String json = sb.toString().trim();
        if (json.isEmpty()) {
            System.out.println("No input provided on STDIN.");
            return;
        }

        ParsedInput inp = parseJson(json);

        // Basic validation
        if (inp.points.size() < inp.k) {
            System.out.println("Not enough shares: got " + inp.points.size() + ", need k=" + inp.k);
            return;
        }

        // Sort by x
        inp.points.sort(Comparator.comparingInt(p -> p.x));

        BestFit best = solve(inp.points, inp.k);

        // Output
        System.out.println("k = " + inp.k + " (degree m = " + (inp.k - 1) + ")");
        System.out.println("Total shares declared (n): " + inp.n + ", shares parsed: " + inp.points.size());
        System.out.println("Best match count among provided shares: " + best.matches);
        System.out.println("Secret (f(0)) = " + best.secret);
        System.out.println("Polynomial f(x) = " + polyToString(best.coeffs));

        // Show any shares that do not lie on the chosen polynomial
        List<Integer> badXs = new ArrayList<>();
        for (Point p : inp.points) {
            Frac v = lagrangeAtX(best.basis, Frac.of(p.x));
            if (!v.equalsInt(p.y)) badXs.add(p.x);
        }
        if (!badXs.isEmpty()) {
            System.out.println("Inconsistent shares at x = " + badXs);
        }
    }
}
