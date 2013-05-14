#include <stdio.h>
#include <float.h>
#include <assert.h>
#include <fenv.h>
#include <math.h>

void dotest_1(int roundingmode, const char *desc)
{
   double eps = DBL_EPSILON;
   double eps14 = eps/4;
   double eps12 = eps/2;
   double eps34 = 3*eps/4;
   double sqrteps = sqrt(eps);
   double sqrteps14 = sqrt(eps14);
   fesetround(roundingmode);
   printf("-- %s --\n", desc);
   printf("eps = %a\n", eps);
   printf("eps14 = %a\n", eps14);
   printf("eps12 = %a\n", eps12);
   printf("eps34 = %a\n", eps34);
   printf("sqrteps = %a\n", sqrteps);
   printf("sqrteps14 = %a\n", sqrteps14);
   printf("1 + eps = %a\n", 1 + eps);
   printf("1 - eps = %a\n", 1 - eps);
   printf("1 + eps14 = %a\n", 1 + eps14);
   printf("1 - eps14 = %a\n", 1 - eps14);
   printf("1 + eps12 = %a\n", 1 + eps12);
   printf("1 - eps12 = %a\n", 1 - eps12);
   printf("1 + eps34 = %a\n", 1 + eps34);
   printf("1 - eps34 = %a\n", 1 - eps34);
   printf("-1 + eps = %a\n", -1 + eps);
   printf("-1 - eps = %a\n", -1 - eps);
   printf("-1 + eps14 = %a\n", -1 + eps14);
   printf("-1 - eps14 = %a\n", -1 - eps14);
   printf("-1 + eps12 = %a\n", -1 + eps12);
   printf("-1 - eps12 = %a\n", -1 - eps12);
   printf("-1 + eps34 = %a\n", -1 + eps34);
   printf("-1 - eps34 = %a\n", -1 - eps34);
   printf("(1 + sqrteps)^2 = %a\n", (1+sqrteps)*(1+sqrteps));
   printf("(1 + sqrteps14)^2 = %a\n", (1+sqrteps14)*(1+sqrteps14));
   printf("1 / (1+eps) = %a\n", 1 / (1+eps));
}

#define dotest(mode) dotest_1(mode, #mode)

int main ()
{
   dotest(FE_TONEAREST);
   dotest(FE_UPWARD);
   dotest(FE_DOWNWARD);
   dotest(FE_TOWARDZERO);

   return 0;
}
