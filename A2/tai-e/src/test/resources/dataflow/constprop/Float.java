class Float {
    public int p;

    void whileConstant() {
        int a, b = -128;
        //long c, d = 1l;
        boolean e, f = true, g = false;
        int i = 0;
        while (i < 10) {
            a = b >>> 1;
            e = (a >= b);
            ++i;
        }
    }
}