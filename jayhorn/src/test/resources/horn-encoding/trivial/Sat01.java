class A
{
  public static int i;
};

class Sat01
{
  public static void main(String[] args)
  {
    assert A.i == 0;
//    A.i = 999;
//    assert A.i == 999;
  }
}
