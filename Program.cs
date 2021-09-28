using System;
using System.Windows;

namespace Hello_World_in_CSharp
{
    class Program
    {
        // static Array mark = new Array<int>;
        static int[] mark;
        static string name;
        static int age;

        static void Main()
        {
            // This Program is for printing Hello World.
            // int a;
            Console.Out.WriteLine("Rechner\n========");
            int a, b;
            MiniTaschenrechner rechner = new MiniTaschenrechner();

            a = Convert.ToInt32(Console.In.ReadLine());
            b = Convert.ToInt32(Console.In.ReadLine());
            Console.Out.WriteLine(rechner.add(a, b));
            Console.Out.WriteLine(rechner.sub(a, b));
            Console.Out.WriteLine(rechner.mult(a, b));
            var p = rechner.div(a, b);
            Console.Out.WriteLine("Division: " + p.First + " Module: " + p.Second);

            Console.In.ReadLine();
        }
    }

    class MiniTaschenrechner
    {
        public int add(int a, int b)
        {
            return a + b;
        }

        public int sub(int a, int b)
        {
            return a - b;
        }

        public int mult(int a, int b)
        {
            return a * b;
        }

        public Pair<int, int> div(int a, int b)
        {
            return new Pair<int, int>(a / b, a % b);
        }
    }

    public class Pair<TFirst, TSecond>
    {
        public TFirst First { get; }
        public TSecond Second { get; }

        public Pair(TFirst first, TSecond second) =>
            (First, Second) = (first, second);
    }
}
