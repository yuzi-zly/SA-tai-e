class UnreachableSwitchBranch1 {

    void lookupSwitch() {
        int x = 1;
        int y = x << 2;
        switch (y) {
            case 2:
                use(2);
                break;  // unreachable case
            case 4:
                use(4);
            case 8:
                use(8);
                break;
            default:
                use(666);
                break; // unreachable case
        }
    }

    void use(int x) {
    }
}
