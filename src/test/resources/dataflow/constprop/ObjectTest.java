class OB {
    public static int si = 10;
    public int i;
    public int getI(){
        return i;
    }
}

class ObjectTest {
    void test(){
        OB ob = new OB();
        ob.i = 1;
        int a = ob.getI();
        int b = ob.i;
        int c = OB.si;
    }
}