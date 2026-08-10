repeat(td(once(unfold))); 
td(once(speculate{push barista::customer_impl::state::idle equal}));
td(once(speculate{push barista::customer_impl::state::thirsty equal}));
td(once(speculate{push barista::customer_impl::state::ordered equal}));
td(once(speculate{push barista::customer_impl::state::has_coffee equal}));
td(once(speculate{dip 1 { pick 0 push barista::customer_impl::state::thirsty equal}}));
must(else(3, at(1, introduce{pick 0 push barista::customer_impl::state::thirsty equal })));
else(3, at(1, inv(flatten)));
else(3, at(2, inv(flatten)));
else(3, at(3, inv(flatten)));

repeat(td(once(factor) | once(sink) | once(fuse)));


id