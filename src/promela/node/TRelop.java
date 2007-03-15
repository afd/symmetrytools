/* This file was generated by SableCC (http://www.sablecc.org/). */

package src.promela.node;

import src.promela.analysis.*;

@SuppressWarnings("nls")
public final class TRelop extends Token
{
    public TRelop(String text)
    {
        setText(text);
    }

    public TRelop(String text, int line, int pos)
    {
        setText(text);
        setLine(line);
        setPos(pos);
    }

    @Override
    public Object clone()
    {
      return new TRelop(getText(), getLine(), getPos());
    }

    public void apply(Switch sw)
    {
        ((Analysis) sw).caseTRelop(this);
    }
}
