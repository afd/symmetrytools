/* This file was generated by SableCC (http://www.sablecc.org/). */

package src.promela.node;

import src.promela.analysis.*;

@SuppressWarnings("nls")
public final class THidden extends Token
{
    public THidden()
    {
        super.setText("hidden");
    }

    public THidden(int line, int pos)
    {
        super.setText("hidden");
        setLine(line);
        setPos(pos);
    }

    @Override
    public Object clone()
    {
      return new THidden(getLine(), getPos());
    }

    public void apply(Switch sw)
    {
        ((Analysis) sw).caseTHidden(this);
    }

    @Override
    public void setText(@SuppressWarnings("unused") String text)
    {
        throw new RuntimeException("Cannot change THidden text.");
    }
}
