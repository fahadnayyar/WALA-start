package com.ibm.wala.examples.testcases;

public class Test1 {
    public static void main(String[] args) {
        int x, y, z;
        x = 10;
        y = x+9;
        z = x*y;
        while (x<z) {
            y++;
            z--;
            if (z==0)
                return;
        }
        System.out.println(x+y+z);
        return;
    }
}