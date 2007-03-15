/* This file was generated by SableCC (http://www.sablecc.org/). */

package src.promela.node;

import src.promela.analysis.*;

@SuppressWarnings("nls")
public final class TNp extends Token
{
    public TNp()
    {
        super.setText("np_");
    }

    public TNp(int line, int pos)
    {
        super.setText("np_");
        setLine(line);
        setPos(pos);
    }

    @Override
    public Object clone()
    {
      return new TNp(getLine(), getPos());
    }

    public void apply(Switch sw)
    {
        ((Analysis) sw).caseTNp(this);
    }

    @Override
    public void setText(@SuppressWarnings("unused") String text)
    {
        throw new RuntimeException("Cannot change TNp text.");
    }
}
