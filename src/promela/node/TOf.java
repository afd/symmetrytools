/* This file was generated by SableCC (http://www.sablecc.org/). */

package src.promela.node;

import src.promela.analysis.*;

@SuppressWarnings("nls")
public final class TOf extends Token
{
    public TOf()
    {
        super.setText("of");
    }

    public TOf(int line, int pos)
    {
        super.setText("of");
        setLine(line);
        setPos(pos);
    }

    @Override
    public Object clone()
    {
      return new TOf(getLine(), getPos());
    }

    public void apply(Switch sw)
    {
        ((Analysis) sw).caseTOf(this);
    }

    @Override
    public void setText(@SuppressWarnings("unused") String text)
    {
        throw new RuntimeException("Cannot change TOf text.");
    }
}
