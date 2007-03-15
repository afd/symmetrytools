/* This file was generated by SableCC (http://www.sablecc.org/). */

package src.promela.node;

import src.promela.analysis.*;

@SuppressWarnings("nls")
public final class TPid extends Token
{
    public TPid()
    {
        super.setText("pid");
    }

    public TPid(int line, int pos)
    {
        super.setText("pid");
        setLine(line);
        setPos(pos);
    }

    @Override
    public Object clone()
    {
      return new TPid(getLine(), getPos());
    }

    public void apply(Switch sw)
    {
        ((Analysis) sw).caseTPid(this);
    }

    @Override
    public void setText(@SuppressWarnings("unused") String text)
    {
        throw new RuntimeException("Cannot change TPid text.");
    }
}
