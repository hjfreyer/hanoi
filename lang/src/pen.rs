pub struct Pen<Value>(Vec<Option<Value>>);

pub trait PenRef<Value>: Into<usize> + From<usize> + Copy {
    fn push(pen: &mut Pen<Value>, v: Value) -> Self {
        pen.push(v)
    }

    fn take(self, pen: &mut Pen<Value>) -> Value {
        pen.take(self)
    }

    fn get(self, pen: &Pen<Value>) -> &Value {
        pen.get(self)
    }

    fn get_mut(self, pen: &mut Pen<Value>) -> &mut Value {
        pen.get_mut(self)
    }
}

impl<Value> Pen<Value> {
    pub fn new() -> Self {
        Self(vec![])
    }
    fn push<Ref: PenRef<Value>>(&mut self, v: Value) -> Ref {
        let idx = self.0.len();
        self.0.push(Some(v));
        Ref::from(idx)
    }

    fn take<Ref: PenRef<Value>>(&mut self, r: Ref) -> Value {
        let opt: &mut Option<Value> = self.0.get_mut(r.into()).unwrap();
        opt.take().unwrap()
    }

    fn get<Ref: PenRef<Value>>(&self, r: Ref) -> &Value {
        self.0.get(r.into()).unwrap().as_ref().unwrap()
    }

    fn get_mut<Ref: PenRef<Value>>(&mut self, r: Ref) -> &mut Value {
        self.0.get_mut(r.into()).unwrap().as_mut().unwrap()
    }
}

pub trait PennedBy: Sized {
    type Ref: PenRef<Self>;
    fn into_pen(self, p: &mut Pen<Self>) -> Self::Ref {
        p.push(self)
    }
}
