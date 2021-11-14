_(function bool P(int i, int p))

void test(int j, int o);
    _(lemma) _(pure)
    _(ensures P(j, o))

void baz()
    _(ensures forall int k. P(k,2))
{
    int z = 0;
    z++;
    z++;
    _(apply forall int h. test(h, z))
} 