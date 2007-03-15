/* This file was generated by SableCC (http://www.sablecc.org/). */

package src.promela.node;

import src.promela.analysis.*;

@SuppressWarnings("nls")
public final class TRightarrow extends Token
{
    public TRightarrow()
    {
        super.setText("->");
    }

    public TRightarrow(int line, int pos)
    {
        super.setText("->");
        setLine(line);
        setPos(pos);
    }

    @Override
    public Object clone()
    {
      return new TRightarrow(getLine(), getPos());
    }

    public void apply(Switch sw)
    {
        ((Analysis) sw).caseTRightarrow(this);
    }

    @Override
    public void setText(@SuppressWarnings("unused") String text)
    {
        throw new RuntimeException("Cannot change TRightarrow text.");
    }
}
