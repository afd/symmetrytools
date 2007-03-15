/* This file was generated by SableCC (http://www.sablecc.org/). */

package src.promela.node;

import src.promela.analysis.*;

@SuppressWarnings("nls")
public final class TQuery extends Token
{
    public TQuery()
    {
        super.setText("?");
    }

    public TQuery(int line, int pos)
    {
        super.setText("?");
        setLine(line);
        setPos(pos);
    }

    @Override
    public Object clone()
    {
      return new TQuery(getLine(), getPos());
    }

    public void apply(Switch sw)
    {
        ((Analysis) sw).caseTQuery(this);
    }

    @Override
    public void setText(@SuppressWarnings("unused") String text)
    {
        throw new RuntimeException("Cannot change TQuery text.");
    }
}
