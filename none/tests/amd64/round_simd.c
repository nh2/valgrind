#include <stdio.h>
#include <float.h>
#include <assert.h>
#include <fenv.h>
#include <math.h>

/*
 * We use GCC vector extensions (the vector_size attribute) to keep
 * the code as generic as possible.  The only exception here is the
 * sqrt function; as of this writing there does not seem to be a way
 * of getting the compiler to emit vsqrtp[sd] short of inline
 * assembly.
 *
 * This means that at least in theory (given perfect GCC machine
 * support) this test program will use instructions corresponding to
 * all (!) of the Iop_{Add,Sub,Mul,Div}{32,64}Fx{2,4,8} on any
 * platform that has them.  With the extra handwritten assembly it
 * will in addition also use Sqrt{32,64}Fx{2,4,8}.
 *
 * Of course the dependence on GCC support means that before you copy
 * this to another arch, you should verify that GCC does in fact emit
 * the instructions you want to test for.
 *
 * The major complication comes from C++ support for the vector types
 * being incomplete as of GCC 4.7.  In particular the implicit cast
 * from a scalar to a vector in expressions like 1+eps did not work
 * for me.  So we use C, at the cost of silly contortions.
 */

#define definetype_1(T, width, V) typedef T V __attribute__ ((vector_size (width)));
#define definetype(typ, width) definetype_1(typ, width, v##width##typ)

definetype(float, 8)
definetype(float, 16)
definetype(float, 32)
definetype(double, 16)
definetype(double, 32)

v8float sqrt_v8float(v8float x) {
   v8float r;
   int i;
   for (i = 0; i < 2; i++)
      r[i] = sqrtf(x[i]);
   return r;
}
v16float sqrt_v16float(v16float x) {
   v16float r;
#ifdef __SSE__
   __asm__ __volatile__ ("sqrtps %1, %0" : "=x"(r) : "xm"(x));
#else
   int i;
   for (i = 0; i < 4; i++)
      r[i] = sqrtf(x[i]);
#endif
   return r;
}
v32float sqrt_v32float(v32float x) {
   v32float r;
#ifdef __AVX__
   __asm__ __volatile__ ("vsqrtps %1, %0" : "=x"(r) : "xm"(x));
#else
   int i;
   for (i = 0; i < 8; i++)
      r[i] = sqrtf(x[i]);
#endif
   return r;
}
v16double sqrt_v16double(v16double x) {
   v16double r;
#ifdef __SSE2__
   __asm__ __volatile__ ("sqrtpd %1, %0" : "=x"(r) : "xm"(x));
#else
   int i;
   for (i = 0; i < 2; i++)
      r[i] = sqrt(x[i]);
#endif
   return r;
}
v32double sqrt_v32double(v32double x) {
   v32double r;
#ifdef __AVX__
   __asm__ __volatile__ ("vsqrtpd %1, %0" : "=x"(r) : "xm"(x));
#else
   int i;
   for (i = 0; i < 4; i++)
      r[i] = sqrt(x[i]);
#endif
   return r;
}

#define definetest_1(T, width, V, epsilon)                              \
                                                                        \
   void printvec_##V(int n, const char *prefix, V vec)                  \
   {                                                                    \
      int i;                                                            \
      printf("%s =", prefix);                                           \
      for (i = 0; i < n; i++)                                           \
         printf(" %a", vec[i]);                                         \
      putchar('\n');                                                    \
   }                                                                    \
                                                                        \
   void dotest_##V(int roundingmode, const char *desc)                  \
   {                                                                    \
      const int n = width / sizeof(T);                                  \
      int i;                                                            \
      V eps;                                                            \
      for (i = 0; i < n; i++) {                                         \
         eps[i] = epsilon;                                              \
      }                                                                 \
      V eps14 = eps/4.f;                                                \
      V eps12 = eps/2.f;                                                \
      V eps34 = 3.f*eps/4.f;                                            \
      V sqrteps = sqrt_##V(eps);                                        \
      V sqrteps14 = sqrt_##V(eps14);                                    \
      fesetround(roundingmode);                                         \
      printf("-- %s --\n", desc);                                       \
      printvec_##V(n, "eps = ", eps);                                   \
      printvec_##V(n, "eps14 = ", eps14);                               \
      printvec_##V(n, "eps12 = ", eps12);                               \
      printvec_##V(n, "eps34 = ", eps34);                               \
      printvec_##V(n, "sqrteps = ", sqrteps);                           \
      printvec_##V(n, "sqrteps14 = ", sqrteps14);                       \
      printvec_##V(n, "1 + eps = ", 1.f + eps);                         \
      printvec_##V(n, "1 - eps = ", 1.f - eps);                         \
      printvec_##V(n, "1 + eps14 = ", 1.f + eps14);                     \
      printvec_##V(n, "1 - eps14 = ", 1.f - eps14);                     \
      printvec_##V(n, "1 + eps12 = ", 1.f + eps12);                     \
      printvec_##V(n, "1 - eps12 = ", 1.f - eps12);                     \
      printvec_##V(n, "1 + eps34 = ", 1.f + eps34);                     \
      printvec_##V(n, "1 - eps34 = ", 1.f - eps34);                     \
      printvec_##V(n, "-1 + eps = ", -1.f + eps);                       \
      printvec_##V(n, "-1 - eps = ", -1.f - eps);                       \
      printvec_##V(n, "-1 + eps14 = ", -1.f + eps14);                   \
      printvec_##V(n, "-1 - eps14 = ", -1.f - eps14);                   \
      printvec_##V(n, "-1 + eps12 = ", -1.f + eps12);                   \
      printvec_##V(n, "-1 - eps12 = ", -1.f - eps12);                   \
      printvec_##V(n, "-1 + eps34 = ", -1.f + eps34);                   \
      printvec_##V(n, "-1 - eps34 = ", -1.f - eps34);                   \
      printvec_##V(n, "(1 + sqrteps)^2 = ", (1+sqrteps)*(1+sqrteps));   \
      printvec_##V(n, "(1 + sqrteps14)^2 = ", (1+sqrteps14)*(1+sqrteps14)); \
      printvec_##V(n, "1 / (1+eps) = ", 1.f / (1+eps));                 \
   }

#define definetest(typ, width, epsilon) definetest_1(typ, width, v##width##typ, epsilon)

definetest(float, 8, FLT_EPSILON)
definetest(float, 16, FLT_EPSILON)
definetest(float, 32, FLT_EPSILON)
definetest(double, 16, DBL_EPSILON)
definetest(double, 32, DBL_EPSILON)

#define dotest(mode, typ, width) dotest_v##width##typ(mode, #mode " " #width " " #typ)

int main ()
{
   dotest(FE_TONEAREST, float, 8);
   dotest(FE_TONEAREST, float, 16);
   dotest(FE_TONEAREST, float, 32);
   dotest(FE_TONEAREST, double, 16);
   dotest(FE_TONEAREST, double, 32);

   dotest(FE_UPWARD, float, 8);
   dotest(FE_UPWARD, float, 16);
   dotest(FE_UPWARD, float, 32);
   dotest(FE_UPWARD, double, 16);
   dotest(FE_UPWARD, double, 32);

   dotest(FE_DOWNWARD, float, 8);
   dotest(FE_DOWNWARD, float, 16);
   dotest(FE_DOWNWARD, float, 32);
   dotest(FE_DOWNWARD, double, 16);
   dotest(FE_DOWNWARD, double, 32);

   dotest(FE_TOWARDZERO, float, 8);
   dotest(FE_TOWARDZERO, float, 16);
   dotest(FE_TOWARDZERO, float, 32);
   dotest(FE_TOWARDZERO, double, 16);
   dotest(FE_TOWARDZERO, double, 32);

   return 0;
}
