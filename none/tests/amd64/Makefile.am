
include $(top_srcdir)/Makefile.tool-tests.am

dist_noinst_SCRIPTS = filter_cpuid filter_stderr gen_insn_test.pl

CLEANFILES = $(addsuffix .c,$(INSN_TESTS))

INSN_TESTS = insn_basic insn_mmx insn_sse insn_sse2 insn_fpu
if BUILD_SSE3_TESTS
 INSN_TESTS += insn_sse3
endif
if BUILD_SSSE3_TESTS
 INSN_TESTS += insn_ssse3
endif
if BUILD_PCLMULQDQ_TESTS
 INSN_TESTS += insn_pclmulqdq
endif

# Explicitly include insn_sse3 even if ! BUILD_SSE3_TESTS, 
# to avoid packaging screwups if 'make dist' is run on a machine
# which failed the BUILD_SSE3_TESTS test in configure.in.

EXTRA_DIST = \
	aes.vgtest aes.stdout.exp aes.stderr.exp \
	amd64locked.vgtest amd64locked.stdout.exp amd64locked.stderr.exp \
	avx-1.vgtest avx-1.stdout.exp avx-1.stderr.exp \
	avx2-1.vgtest avx2-1.stdout.exp avx2-1.stderr.exp \
	asorep.stderr.exp asorep.stdout.exp asorep.vgtest \
	bmi.stderr.exp bmi.stdout.exp bmi.vgtest \
	fma.stderr.exp fma.stdout.exp fma.vgtest \
	bug127521-64.vgtest bug127521-64.stdout.exp bug127521-64.stderr.exp \
	bug132813-amd64.vgtest bug132813-amd64.stdout.exp \
	bug132813-amd64.stderr.exp \
	bug137714-amd64.vgtest bug137714-amd64.stdout.exp \
	bug137714-amd64.stderr.exp \
	bug132918.vgtest bug132918.stderr.exp bug132918.stdout.exp \
	bug132918.stdout.exp-older-glibc \
	bug156404-amd64.vgtest bug156404-amd64.stdout.exp \
	bug156404-amd64.stderr.exp \
	clc.vgtest clc.stdout.exp clc.stderr.exp \
	crc32.vgtest crc32.stdout.exp crc32.stderr.exp \
	cmpxchg.vgtest cmpxchg.stdout.exp cmpxchg.stderr.exp \
	faultstatus.disabled faultstatus.stderr.exp \
	fcmovnu.vgtest fcmovnu.stderr.exp fcmovnu.stdout.exp \
	fxtract.vgtest fxtract.stderr.exp fxtract.stdout.exp \
	fxtract.stdout.exp-older-glibc \
	$(addsuffix .stderr.exp,$(INSN_TESTS)) \
	$(addsuffix .stdout.exp,$(INSN_TESTS)) \
	$(addsuffix .vgtest,$(INSN_TESTS)) \
	insn_pclmulqdq.vgtest insn_pclmulqdq.stdout.exp \
	insn_pclmulqdq.stderr.exp \
	insn_sse3.stdout.exp insn_sse3.stderr.exp insn_sse3.vgtest \
	insn_ssse3.stdout.exp insn_ssse3.stderr.exp insn_ssse3.vgtest \
	jrcxz.stderr.exp jrcxz.stdout.exp jrcxz.vgtest \
	looper.stderr.exp looper.stdout.exp looper.vgtest \
	loopnel.stderr.exp loopnel.stdout.exp loopnel.vgtest \
	lzcnt64.stderr.exp lzcnt64.stdout.exp lzcnt64.vgtest \
	movbe.stderr.exp movbe.stdout.exp movbe.vgtest \
	nan80and64.stderr.exp nan80and64.stdout.exp nan80and64.vgtest \
	nibz_bennee_mmap.stderr.exp nibz_bennee_mmap.stdout.exp \
	nibz_bennee_mmap.vgtest \
	pcmpstr64.stderr.exp pcmpstr64.stdout.exp \
	pcmpstr64.vgtest \
	pcmpstr64w.stderr.exp pcmpstr64w.stdout.exp \
	pcmpstr64w.vgtest \
	pcmpxstrx64.stderr.exp pcmpxstrx64.stdout.exp \
	pcmpxstrx64.vgtest \
	pcmpxstrx64w.stderr.exp pcmpxstrx64w.stdout.exp \
	pcmpxstrx64w.vgtest \
	rcl-amd64.vgtest rcl-amd64.stdout.exp rcl-amd64.stderr.exp \
	redundantRexW.vgtest redundantRexW.stdout.exp \
	redundantRexW.stderr.exp \
	round.stderr.exp round.stdout.exp round.vgtest \
	round_simd.stderr.exp round_simd.stdout.exp \
	round_simd_sse.stderr.exp round_simd_sse.stdout.exp round_simd_sse.vgtest \
	round_simd_sse2.stderr.exp round_simd_sse2.stdout.exp round_simd_sse2.vgtest \
	round_simd_avx.stderr.exp round_simd_avx.stdout.exp round_simd_avx.vgtest \
	smc1.stderr.exp smc1.stdout.exp smc1.vgtest \
	sbbmisc.stderr.exp sbbmisc.stdout.exp sbbmisc.vgtest \
	shrld.stderr.exp shrld.stdout.exp shrld.vgtest \
	ssse3_misaligned.stderr.exp ssse3_misaligned.stdout.exp \
	ssse3_misaligned.vgtest \
	sse4-64.stderr.exp sse4-64.stdout.exp sse4-64.vgtest \
	sse4-64.stdout.exp-older-glibc \
	slahf-amd64.stderr.exp slahf-amd64.stdout.exp \
	slahf-amd64.vgtest \
	xadd.stderr.exp xadd.stdout.exp xadd.vgtest

check_PROGRAMS = \
	allexec \
	amd64locked \
	asorep \
	bug127521-64 bug132813-amd64 bug132918 \
	clc \
	cmpxchg \
	$(INSN_TESTS) \
	nan80and64 \
	rcl-amd64 \
	redundantRexW \
	round \
	smc1 \
	sbbmisc \
	nibz_bennee_mmap \
	xadd
if BUILD_SSSE3_TESTS
 check_PROGRAMS += ssse3_misaligned
endif
if BUILD_LZCNT_TESTS
 check_PROGRAMS += lzcnt64
endif
if BUILD_SSE42_TESTS
 check_PROGRAMS += \
	pcmpstr64 pcmpxstrx64 sse4-64 crc32 aes \
	pcmpstr64w pcmpxstrx64w
endif
if BUILD_AVX_TESTS
if BUILD_VPCLMULQDQ_TESTS
 check_PROGRAMS += avx-1
endif
endif
if BUILD_AVX2_TESTS
  check_PROGRAMS += avx2-1
endif
if BUILD_BMI_TESTS
 check_PROGRAMS += bmi
endif
if BUILD_FMA_TESTS
 check_PROGRAMS += fma
endif
if BUILD_MOVBE_TESTS
 check_PROGRAMS += movbe
endif

# DDD: these need to be made to work on Darwin like the x86/ ones were.
if ! VGCONF_OS_IS_DARWIN
   check_PROGRAMS += \
	bug137714-amd64 \
	bug156404-amd64 \
	faultstatus \
	fcmovnu \
	fxtract \
	looper \
	loopnel \
	jrcxz \
	shrld \
	slahf-amd64
endif

AM_CFLAGS    += @FLAG_M64@
AM_CXXFLAGS  += @FLAG_M64@
AM_CCASFLAGS += @FLAG_M64@

allexec_CFLAGS		= $(AM_CFLAGS) @FLAG_W_NO_NONNULL@

# generic C ones
amd64locked_CFLAGS	= $(AM_CFLAGS) -O
bug132918_LDADD		= -lm
fxtract_CFLAGS		= $(AM_CFLAGS) @FLAG_W_NO_OVERFLOW@
insn_basic_SOURCES	= insn_basic.def
insn_basic_LDADD	= -lm
insn_mmx_SOURCES	= insn_mmx.def
insn_mmx_LDADD		= -lm
insn_sse_SOURCES	= insn_sse.def
insn_sse_LDADD		= -lm
insn_sse2_SOURCES	= insn_sse2.def
insn_sse2_LDADD		= -lm
insn_sse3_SOURCES	= insn_sse3.def
insn_sse3_LDADD		= -lm
insn_ssse3_SOURCES	= insn_ssse3.def
insn_ssse3_LDADD	= -lm
insn_fpu_SOURCES	= insn_fpu.def
insn_fpu_LDADD		= -lm
insn_pclmulqdq_SOURCES  = insn_pclmulqdq.def
fxtract_LDADD		= -lm
round_CFLAGS		= -frounding-math
round_LDADD		= -lm

if BUILD_GCC_SIMD_TESTS
if BUILD_FESETROUND_TESTS
# We build various versions of the SIMD rounding mode test: SSE for
# ADDPS and friends; SSE2 for *PD; AVX for V*PS and V*PD
if BUILD_SSE_TESTS
check_PROGRAMS += round_simd_sse
round_simd_sse_SOURCES	= round_simd.c
round_simd_sse_CFLAGS	= -frounding-math -O2 -msse
round_simd_sse_LDADD	= -lm
endif

if BUILD_SSE2_TESTS
check_PROGRAMS += round_simd_sse2
round_simd_sse2_SOURCES	= round_simd.c
round_simd_sse2_CFLAGS	= -frounding-math -O2 -msse2
round_simd_sse2_LDADD	= -lm
endif

if BUILD_AVX2_TESTS
check_PROGRAMS += round_simd_avx
round_simd_avx_SOURCES	= round_simd.c
round_simd_avx_CFLAGS	= -frounding-math -O2 -mavx
round_simd_avx_LDADD	= -lm
endif

endif # BUILD_FESETROUND_TESTS
endif # BUILD_GCC_SIMD_TESTS

.def.c: $(srcdir)/gen_insn_test.pl
	$(PERL) $(srcdir)/gen_insn_test.pl < $< > $@
